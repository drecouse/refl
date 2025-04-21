#include <clang/AST/Type.h>
#include <clang/Basic/AttrKinds.h>
#include <clang/Basic/LangOptions.h>
#include <clang/Basic/ParsedAttrInfo.h>
#include <clang/Basic/Specifiers.h>
#include <llvm/Support/raw_ostream.h>
#include <string>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/FormatVariadic.h"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace clang;
using namespace llvm;

template <typename IT>
inline void compile(CompilerInstance* CI, std::string const& FileName, IT FileBegin, IT FileEnd)
{
    auto& Diagnostics{CI->getDiagnostics()};
    if (Diagnostics.getNumErrors() > 0)
        return;

    auto& CodeGenOpts{CI->getCodeGenOpts()};
    auto& Target{CI->getTarget()};

    // create new compiler instance
    auto CInvNew{std::make_shared<CompilerInvocation>()};

    std::vector<const char*> args;
    for (auto& it : CodeGenOpts.CommandLineArgs) {
        args.push_back(it.c_str());
    }

    bool CInvNewCreated{
        CompilerInvocation::CreateFromArgs(*CInvNew, args, Diagnostics)
    };

    assert(CInvNewCreated);

    CompilerInstance CINew;
    CINew.setInvocation(CInvNew);
    CINew.setTarget(&Target);
    CINew.createDiagnostics(CI->getVirtualFileSystem());

    // create rewrite buffer
    std::string FileContent{FileBegin, FileEnd};
    auto FileMemoryBuffer{MemoryBuffer::getMemBufferCopy(FileContent)};

    // create "virtual" input file
    auto& PreprocessorOpts{CINew.getPreprocessorOpts()};
    PreprocessorOpts.addRemappedFile(FileName, FileMemoryBuffer.get());

    // generate code
    EmitObjAction EmitObj;
    CINew.ExecuteAction(EmitObj);

    auto _ = FileMemoryBuffer.release(); // intentionally not freed
}

enum class ReflSpec { all,
                      none,
                      include,
                      exclude,
                      tag,
                      unknown };

static ReflSpec getReflSpec(const Decl* decl, const SourceManager& SourceManager, ASTContext& Context_)
{
    const auto& attrs = decl->getAttrs();
    for (auto a : attrs) {
        if (!strcmp(a->getSpelling(), "annotate")) {
            auto s = static_cast<std::string_view>(Lexer::getSourceText(
                CharSourceRange::getTokenRange(a->getRange()), SourceManager,
                Context_.getLangOpts()
            ));
            if (s.starts_with("refl_"))
                return ReflSpec::tag;
            if (s.starts_with("refl::")) {
                if (s.ends_with("all"))
                    return ReflSpec::all;
                else if (s.ends_with("none"))
                    return ReflSpec::none;
                else if (s.ends_with("include"))
                    return ReflSpec::include;
                else if (s.ends_with("exclude"))
                    return ReflSpec::exclude;
            }
        }
    }
    return ReflSpec::unknown;
}

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wweak-vtables"
#pragma clang diagnostic ignored "-Wunused-parameter"

AST_MATCHER_P(Decl, hasReflectAttr, const char*, AttrName)
{
    auto Policy = PrintingPolicy{LangOptions{}};
    for (const auto* Attr : Node.attrs()) {
        std::string attr_name(Attr->getSpelling());
        std::string attr_annotate("annotate");
        std::string attr_my(AttrName);
        if (attr_name == attr_annotate) {
            std::string SS;
            raw_string_ostream S(SS);
            Attr->printPretty(S, Policy);
            std::string attr_string(S.str());
            if (attr_string.find(attr_my) != std::string::npos) {
                return true;
            }
        }
    }
    return false;
}

AST_MATCHER_P(VarDecl, isStaticFieldOf, const RecordDecl*, Record)
{
    if (Node.isDefinedOutsideFunctionOrMethod()) {
        auto ctx = Node.getDeclContext();
        if (isa<RecordDecl>(ctx)) {
            auto r = static_cast<const RecordDecl*>(ctx);
            return Record == r;
        }
    }
    return false;
}

#pragma clang diagnostic pop

class ReflError : public std::exception {
public:
    ReflError(std::string const& What, SourceLocation const& Where)
        : What_(What)
        , Where_(Where)
    {
    }

    template <typename T>
    ReflError(std::string const& What, T const* Where)
        : ReflError(What, Where->getBeginLoc())
    {
    }

    char const* what() const noexcept override;

    SourceLocation where() const noexcept { return Where_; }

private:
    std::string What_;
    SourceLocation Where_;
};

char const* ReflError::what() const noexcept
{
    return What_.c_str();
}

template <typename C>
class ReflStaticMatchCallback
    : public ast_matchers::MatchFinder::MatchCallback {
public:
    ReflStaticMatchCallback(C&& callback)
        : callback{std::forward<C>(callback)}
    {
    }
    void
    run(ast_matchers::MatchFinder::MatchResult const& Result) override
    {
        callback(Result);
    }
    C callback;
};
template <typename C> ReflStaticMatchCallback(C) -> ReflStaticMatchCallback<C>;

class ReflRecordMatchCallback
    : public ast_matchers::MatchFinder::MatchCallback {
public:
    ReflRecordMatchCallback(ASTContext& Context, FileID* FileID, Rewriter* FileRewriter)
        : Context_(Context)
        , FileID_(FileID)
        , FileRewriter_(FileRewriter)
    {
    }
    void run(ast_matchers::MatchFinder::MatchResult const& Result) override;

private:
    std::set<void*> unique;
    ASTContext& Context_;
    FileID* FileID_;
    Rewriter* FileRewriter_;
};

void ReflRecordMatchCallback::run(ast_matchers::MatchFinder::MatchResult const& Result)
{
    auto& SourceManager{Context_.getSourceManager()};
    auto recordDecl{
        Result.Nodes.getNodeAs<CXXRecordDecl>("refl_record")
    };
    auto enumDecl{Result.Nodes.getNodeAs<EnumDecl>("refl_enum")};
    if (recordDecl) {
        if (unique.contains(recordDecl->getLocation().getPtrEncoding()))
            return;
        unique.insert(recordDecl->getLocation().getPtrEncoding());

        auto spec = getReflSpec(recordDecl, SourceManager, Context_);

        const auto& sname = recordDecl->getName();
        const auto& qname = recordDecl->getQualifiedNameAsString();
        std::string ss;
        ss +=
            formatv("public:using _meta=refl::RecordType<{0},\"{0}\",\"{1}\",REFL_TUPLE<", sname, qname);
        {
            for (int i = 0; auto& it : recordDecl->bases()) {
                auto acc = it.getAccessSpecifier();
                const char* str;
                if (acc == AccessSpecifier::AS_private)
                    str = "Private";
                if (acc == AccessSpecifier::AS_public)
                    str = "Public";
                if (acc == AccessSpecifier::AS_protected)
                    str = "Protected";
                if (i++ != 0)
                    ss += ",";
                ss += formatv("refl::Base<{1},refl::AccessSpecifier::{0}>", str, it.getType().getAsString());
            }
        }
        ss += ">,REFL_TUPLE<";
        {
            int i = 0;
            for (const auto it : recordDecl->methods()) {
                if (isa<CXXConstructorDecl>(it) ||
                    isa<CXXDestructorDecl>(it) ||
                    it->isImplicit() || it->isDeleted())
                    continue;
                auto mspec = getReflSpec(it, SourceManager, Context_);
                if (mspec == ReflSpec::exclude)
                    continue;
                if (spec == ReflSpec::none && mspec != ReflSpec::include &&
                    mspec != ReflSpec::tag)
                    continue;
                auto acc = it->getAccess();
                const char* accs;
                switch (acc) {
                case AccessSpecifier::AS_private:
                    accs = "Private";
                    break;
                case AccessSpecifier::AS_public:
                    accs = "Public";
                    break;
                case AccessSpecifier::AS_protected:
                    accs = "Protected";
                    break;
                case AccessSpecifier::AS_none:
                default:
                    errs() << "Unexpected None access specifier\n";
                    assert(false);
                }
                auto str   = it->getNameAsString(); // TODO: deprecated
                auto strq  = it->getQualifiedNameAsString();
                auto ret   = it->getReturnType().getAsString();
                auto found = ret.find("_Bool");
                if (found != std::string::npos) ret.replace(found, 5, "bool ");
                auto qual              = it->getMethodQualifiers().getAsString();
                auto ref               = it->getRefQualifier();
                std::string params     = "";
                std::string paramNames = "";
                for (bool f = false; const auto& p : it->parameters()) {
                    if (f) {
                        params += ',';
                    }
                    f           = true;
                    auto pname  = p->getType().getAsString();
                    auto found2 = pname.find("_Bool");
                    if (found2 != std::string::npos) pname.replace(found2, 5, "bool");
                    params += pname;
                    paramNames += formatv(",\"{0}\"", p->getNameAsString());
                }
                std::string rqual;
                if (ref == RefQualifierKind::RQ_LValue)
                    rqual = formatv("{0} &", qual);
                else if (ref == RefQualifierKind::RQ_RValue)
                    rqual = formatv("{0} &&", qual);
                else
                    rqual = formatv("{0}", qual);

                if (i++ != 0)
                    ss += ',';
                if (it->isInstance()) {
                    ss += formatv("refl::Func<static_cast<{0}({1}::*)", ret, sname);
                } else {
                    ss += formatv("refl::Func<static_cast<{0}(*)", ret);
                }
                ss +=
                    formatv("({0}){6}>(&{1}::{2}),\"{2}\",\"{3}\",\"{2}({0}){6}\",{4}"
                            ",refl::AccessSpecifier::{5},{7},refl::PList<REFL_TUPLE<{8}>{9}>",
                            params, sname, str, strq, it->isVirtual(), accs, rqual, ret, params, paramNames);
                const auto& attrs = it->getAttrs();
                for (auto a : attrs) {
                    if (!strcmp(a->getSpelling(), "annotate")) {
                        auto s = static_cast<std::string_view>(Lexer::getSourceText(
                            CharSourceRange::getTokenRange(a->getRange()),
                            SourceManager, Context_.getLangOpts()
                        ));
                        if (!s.starts_with("refl_tag"))
                            continue;
                        auto f = s.find_first_of('(');
                        auto l = s.find_last_of(')');
                        ss += formatv(",{0}", s.substr(f + 1, l - f - 1));
                    }
                }
                ss += '>';
            }
        }
        ss += ">,REFL_TUPLE<";
        {
            int i = 0;
            for (const auto it : recordDecl->fields()) {
                auto mspec = getReflSpec(it, SourceManager, Context_);
                if (mspec == ReflSpec::exclude)
                    continue;
                if (spec == ReflSpec::none && mspec != ReflSpec::include &&
                    mspec != ReflSpec::tag)
                    continue;
                if (i++ != 0)
                    ss += ',';
                auto str  = it->getNameAsString();
                auto strq = it->getQualifiedNameAsString();
                auto acc  = it->getAccess();
                const char* accs;
                switch (acc) {
                case AccessSpecifier::AS_private:
                    accs = "Private";
                    break;
                case AccessSpecifier::AS_public:
                    accs = "Public";
                    break;
                case AccessSpecifier::AS_protected:
                    accs = "Protected";
                    break;
                case AccessSpecifier::AS_none:
                default:
                    errs() << "Unexpected None access specifier\n";
                    assert(false);
                }
                ss += formatv("refl::Var<&{0}::{1},\"{1}\",\"{2}\",{3},"
                              "refl::AccessSpecifier::{4}",
                              sname, str, strq, it->isMutable(), accs);
                const auto& attrs = it->getAttrs();
                for (auto a : attrs) {
                    if (!strcmp(a->getSpelling(), "annotate")) {
                        auto s = static_cast<std::string_view>(Lexer::getSourceText(
                            CharSourceRange::getTokenRange(a->getRange()),
                            SourceManager, Context_.getLangOpts()
                        ));
                        if (!s.starts_with("refl_tag"))
                            continue;
                        auto f = s.find_first_of('(');
                        auto l = s.find_last_of(')');
                        ss += formatv(",{0}", s.substr(f + 1, l - f - 1));
                    }
                }
                ss += '>';
            }

            using namespace ast_matchers;

            auto ReflectStaticMatchExpression(
                varDecl(isStaticFieldOf(recordDecl))
            );

            ReflStaticMatchCallback match{[&](const auto& res) {
                auto staticDecl{
                    res.Nodes.template getNodeAs<VarDecl>(
                        "refl_static"
                    )
                };
                if (staticDecl) {
                    auto& it = staticDecl;
                    auto mspec =
                        getReflSpec(staticDecl, SourceManager, Context_);
                    bool ok = false;
                    if (spec != ReflSpec::unknown &&
                        (mspec == ReflSpec::include ||
                         mspec == ReflSpec::tag))
                        ok = true;
                    if (spec == ReflSpec::all && mspec != ReflSpec::exclude)
                        ok = true;
                    if (ok) {
                        if (i++ != 0)
                            ss += ',';
                        auto str  = it->getNameAsString();
                        auto strq = it->getQualifiedNameAsString();
                        auto acc  = it->getAccess();
                        const char* accs;
                        switch (acc) {
                        case AccessSpecifier::AS_private:
                            accs = "Private";
                            break;
                        case AccessSpecifier::AS_public:
                            accs = "Public";
                            break;
                        case AccessSpecifier::AS_protected:
                            accs = "Protected";
                            break;
                        case AccessSpecifier::AS_none:
                        default:
                            errs() << "Unexpected None access specifier\n";
                            assert(false);
                        }
                        ss += formatv("refl::Var<&{0}::{1},\"{1}\",\"{2}\","
                                      "{3},refl::AccessSpecifier::{4}",
                                      sname, str, strq, false, accs);
                        const auto& attrs = it->getAttrs();
                        for (auto a : attrs) {
                            if (!strcmp(a->getSpelling(), "annotate")) {
                                auto s = static_cast<std::string_view>(Lexer::getSourceText(
                                    CharSourceRange::getTokenRange(
                                        a->getRange()
                                    ),
                                    SourceManager,
                                    Context_.getLangOpts()
                                ));
                                if (!s.starts_with("refl_tag"))
                                    continue;
                                auto f = s.find_first_of('(');
                                auto l = s.find_last_of(')');
                                ss += formatv(",{0}", s.substr(f + 1, l - f - 1));
                            }
                        }
                        ss += '>';
                    }
                }
            }};

            ast_matchers::MatchFinder MatchFinder;
            MatchFinder.addMatcher(
                ReflectStaticMatchExpression.bind("refl_static"), &match
            );
            MatchFinder.matchAST(Context_);
        }

        ss += ">,REFL_TUPLE<";
        {
            for (int f = 0; const auto it : recordDecl->methods()) {
                if (!isa<CXXConstructorDecl>(it) ||
                    it->isDeleted())
                    continue;
                auto mspec = getReflSpec(it, SourceManager, Context_);
                if (mspec == ReflSpec::exclude)
                    continue;
                if (spec == ReflSpec::none && mspec != ReflSpec::include &&
                    mspec != ReflSpec::tag)
                    continue;
                if (f++)
                    ss += ',';
                ss += "refl::Constr<";
                std::string params     = "";
                std::string paramNames = "";
                for (int f1 = 0; const auto& p : it->parameters()) {
                    if (f1++) {
                        params += ',';
                    }
                    auto pname  = p->getType().getAsString();
                    auto found2 = pname.find("_Bool");
                    if (found2 != std::string::npos) pname.replace(found2, 5, "bool");
                    params += pname;
                    paramNames += formatv(",\"{0}\"", p->getNameAsString());
                }
                ss += formatv("\"{1}({0})\",{1},refl::PList<REFL_TUPLE<{0}>{2}>", params, sname, paramNames);
                const auto& attrs = it->getAttrs();
                for (auto a : attrs) {
                    if (!strcmp(a->getSpelling(), "annotate")) {
                        auto s  = static_cast<std::string_view>(Lexer::getSourceText(
                            CharSourceRange::getTokenRange(a->getRange()),
                            SourceManager, Context_.getLangOpts()
                        ));
                        auto f2 = s.find_first_of('(');
                        auto l  = s.find_last_of(')');
                        ss += formatv(",{0}", s.substr(f2 + 1, l - f2 - 1));
                    }
                }
                ss += '>';
            }
        }

        ss += ">>;";

        FileRewriter_->InsertTextAfter(recordDecl->getEndLoc(), ss);
        *FileID_ = SourceManager.getFileID(recordDecl->getBeginLoc());
    } else if (enumDecl) {
        std::string ss;
        const auto& sname = enumDecl->getDeclName();
        const auto& qname = enumDecl->getQualifiedNameAsString();
        int count         = 0;
        for (auto _ : enumDecl->enumerators()) count++;

        ss +=
            formatv("template<>struct refl::meta<{0}>:EnumType<{0},\"{1}\",\"{0}\">{static "
                    "constexpr std::array<refl::Enumerator<{0}>,{2}>enumerators={{",
                    qname, sname, count);

        for (int f = 0; const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            if (f++)
                ss += ',';
            ss += formatv("refl::Enumerator<{0}>{{\"{1}\",{0}::{1}}", qname, n);
        }

        ss += formatv(
            "};static constexpr bool valid({0} v)noexcept{{for(const "
            "auto&e:enumerators)if(e.value==v)return true;return "
            "false;}static constexpr std::string_view to_string({0} "
            "v)noexcept{{switch(v){{",
            qname
        );

        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return\"{1}\";", qname, n);
        }

        ss += formatv("default:{{assert(false);__builtin_unreachable();}}}"
                      "static constexpr std::string_view "
                      "to_string_safe({0} v)noexcept{{switch(v){{",
                      qname);

        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return\"{1}\";", qname, n);
        }

        ss += formatv(
            "default:return{{};}}static constexpr "
            "std::optional<{0}>from_string(std::string_view "
            "n)noexcept{{for(const auto&e:enumerators)if(e.name==n)return "
            "e.value;return std::nullopt;}};",
            qname
        );

        SourceLocation loc;
        const DeclContext* p = enumDecl;
        while (!p->getParent()->isTranslationUnit()) {
            p = p->getParent();
        }
        if (isa<NamespaceDecl>(p)) {
            loc = static_cast<const NamespaceDecl*>(p)
                      ->getEndLoc()
                      .getLocWithOffset(1);
        } else if (isa<TagDecl>(p)) {
            loc = Lexer::findLocationAfterToken(
                      static_cast<const TagDecl*>(p)->getEndLoc(),
                      tok::TokenKind::semi, SourceManager,
                      Context_.getLangOpts(), true
            )
                      .getLocWithOffset(-1);
        }

        if (loc.isValid()) {
            FileRewriter_->InsertTextAfter(loc, ss);
            *FileID_ = SourceManager.getFileID(enumDecl->getBeginLoc());
        }
    }
}

class ReflConsumer : public ASTConsumer {
public:
    ReflConsumer(FileID* FileID, Rewriter* FileRewriter, bool* FileRewriteError)
        : FileID_(FileID)
        , FileRewriter_(FileRewriter)
        , FileRewriteError_(FileRewriteError)
    {
    }

    void HandleTranslationUnit(ASTContext& Context) override;

private:
    FileID* FileID_;
    Rewriter* FileRewriter_;
    bool* FileRewriteError_;
};

void ReflConsumer::HandleTranslationUnit(ASTContext& Context)
{
    using namespace ast_matchers;

    auto ReflectedRecordsMatchExpression(cxxRecordDecl(
        anyOf(hasReflectAttr("none"), hasReflectAttr("all"))
    ));
    auto ReflectedEnumMatchExpression(
        enumDecl(anyOf(hasReflectAttr("none"), hasReflectAttr("all")))
    );

    ReflRecordMatchCallback MatchRecordCallback(Context, FileID_, FileRewriter_);

    ast_matchers::MatchFinder MatchFinder;

    MatchFinder.addMatcher(
        ReflectedRecordsMatchExpression.bind("refl_record"),
        &MatchRecordCallback
    );
    MatchFinder.addMatcher(ReflectedEnumMatchExpression.bind("refl_enum"), &MatchRecordCallback);

    try {
        MatchFinder.matchAST(Context);
        *FileRewriteError_ = false;
    } catch (ReflError const& e) {
        auto& Diags{Context.getDiagnostics()};

        unsigned ID{Diags.getDiagnosticIDs()->getCustomDiagID(
            DiagnosticIDs::Error, e.what()
        )};

        Diags.Report(e.where(), ID);

        *FileRewriteError_ = true;
    }
}


class ReflectAction : public PluginASTAction {
protected:
    std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance& CI, StringRef FileName) override
    {
        auto& SourceManager{CI.getSourceManager()};
        auto& LangOpts{CI.getLangOpts()};

        CI_ = &CI;

        FileName_ = FileName.str();

        FileRewriter_.setSourceMgr(SourceManager, LangOpts);

        return std::make_unique<ReflConsumer>(&FileID_, &FileRewriter_, &FileRewriteError_);
    }

    bool ParseArgs(CompilerInstance const&, std::vector<std::string> const&) override;

    PluginASTAction::ActionType getActionType() override
    {
        return PluginASTAction::ReplaceAction;
    }

    void EndSourceFileAction() override
    {
        if (FileRewriteError_)
            return;

        auto FileRewriteBuffer{FileRewriter_.getRewriteBufferFor(FileID_)};

        compile(CI_, FileName_, FileRewriteBuffer->begin(), FileRewriteBuffer->end());
    }

private:
    CompilerInstance* CI_;

    std::string FileName_;
    FileID FileID_;
    Rewriter FileRewriter_;
    bool FileRewriteError_ = false;
};

bool ReflectAction::ParseArgs(CompilerInstance const&, std::vector<std::string> const&)
{
    return true;
}

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wglobal-constructors"

static FrontendPluginRegistry::Add<ReflectAction>
    X("reflect", "add static reflection to annotated classes");

#pragma clang diagnostic pop

// TODO:
//  templates? specialize manually!
//  outside reflection definiton: how to signal to llvm that the class should be
//      reflected (including arbitrary templated types)
//  refl::public/protected/private?
