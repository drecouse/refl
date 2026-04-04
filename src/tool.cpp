#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/AST/ASTContext.h"
#include <clang/AST/Type.h>
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Execution.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Signals.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/FormatVariadic.h"
#include <filesystem>
#include <fstream>
#include "clang/Tooling/DependencyScanning/DependencyScanningService.h"
#include "clang/Tooling/DependencyScanning/DependencyScanningTool.h"
#include "clang/Tooling/DependencyScanning/DependencyScanningWorker.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/Program.h"

using namespace clang;
//using namespace clang::tooling;
using namespace llvm;
namespace fs = std::filesystem;

#include "utility.hpp"


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
    ReflRecordMatchCallback(std::string baseFolder, std::string metaFolder) : mBase{fs::absolute(baseFolder)}, mMeta{fs::absolute(metaFolder)}
    {
    }
    void run(ast_matchers::MatchFinder::MatchResult const& Result) override;
  
    void onStartOfTranslationUnit() override {
        ss = "";
    }
    void onEndOfTranslationUnit() override {
        //if (ss != "") {
            auto& sm = _ctx->getSourceManager();
            auto fName = sm.getFileEntryForID(sm.getMainFileID())->tryGetRealPathName();
            auto p = fs::absolute(fs::path{fName.str()});
            auto rel = fs::relative(p, mBase);
            auto m = mMeta / rel;
            auto m2 = m;
            fs::create_directories(m2.remove_filename());
            auto f = std::ofstream{m.string() + ".meta.inc"};
            f << ss << "\n";
        //}
    }
    void onTU(ASTContext* ctx) {
        this->_ctx = ctx;
    }

private:
    std::set<void*> unique;
    ASTContext* _ctx;
    std::string ss;
    fs::path mBase, mMeta;
};

// This class substitutes for clang::ast_matchers::MatchFinder by
// arranging to call 'onTU' at the right time.
class MyMatchFinder : public ast_matchers::MatchFinder {
public:      // data
  ReflRecordMatchCallback *m_handleMatch;

public:      // methods
  explicit MyMatchFinder(ReflRecordMatchCallback *handleMatch)
    : m_handleMatch(handleMatch)
  {}

  // This is what 'newFrontendActionFactory' calls.  It is effectively
  // the entry point to the FE action system.
    std::unique_ptr<ASTConsumer> newASTConsumer();

  // This will be invoked by 'MyMatchASTConsumer'/
  void matchAST(ASTContext &context) 
  {
    m_handleMatch->onTU(&context);

    // This does the normal MatchFinder stuff, including calling
    // 'onStartOfTranslationUnit'.
    MatchFinder::matchAST(context);
  }
};

// This class is a substitute for the 'MatchASTConsumer' class defined
// in ASTMatchFinder.cpp, inside the implementation of 'MatchFinder'.
class MyMatchASTConsumer : public ASTConsumer {
public:      // data
  MyMatchFinder *m_myFinder;

public:      // methods
  MyMatchASTConsumer(MyMatchFinder *myFinder)
    : m_myFinder(myFinder)
  {}

private:     // methods
  // This is the ASTConsumer callback we need to override.
    void HandleTranslationUnit(ASTContext& Context) override;
};

void MyMatchASTConsumer::HandleTranslationUnit(ASTContext& Context)
{
    // Call MyMatchFinder::matchAST instead of MatchFinder::matchAST.
    m_myFinder->matchAST(Context);
}


// This has to be defined out of line because it needs the definition
// of 'MyMatchASTConsumer'.
std::unique_ptr<ASTConsumer> MyMatchFinder::newASTConsumer()
{
  return std::make_unique<MyMatchASTConsumer>(this);
}

void ReflRecordMatchCallback::run(ast_matchers::MatchFinder::MatchResult const& Result)
{
    auto& Context_ = *_ctx;
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
        auto macroNameOverride = getReflMacroName(recordDecl, SourceManager, Context_);

        const auto& sname = recordDecl->getName();
        const auto& qname = recordDecl->getQualifiedNameAsString();

        std::string macroName = macroNameOverride;
        auto rec = [&](this const auto& self, const DeclContext* c) -> void {
            auto parent = c->getParent();
            if (parent != nullptr && !parent->isTranslationUnit()) {
                self(parent);
                macroName += "_";
            }
            if (c->isNamespace()) {
                auto n = static_cast<const NamespaceDecl*>(c);
                macroName += n->getName(); 
            } else if (c->isRecord()) {
                auto n = static_cast<const CXXRecordDecl*>(c);
                macroName += n->getName();
                auto plist = n->getDescribedTemplateParams();
                if (plist) {
                    for (auto& it : *plist) {
                        macroName += formatv("_{}", it->getName());
                    }
                }
            }
        };
        if (macroName == "") rec(recordDecl);

        //llvm::outs() << macroName;
        ss +=
            //formatv("namespace refl{template<{2}> struct meta<{3}> : refl::RecordType<{3},\"{0}\",\"{1}\",REFL_TUPLE<", sname, qname, templateSpecList, className);
            formatv("#define REFLG_{2} public:using _meta=refl::RecordType<{0},\"{0}\",\"{1}\",REFL_TUPLE<", sname, qname, macroName);
            //formatv("public:using _meta=refl::RecordType<{0},\"{0}\",\"{1}\",REFL_TUPLE<", sname, qname);
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

        //ss += ">> {};}";
        ss += ">>;\n";
    } else if (enumDecl) {
        const auto& sname = enumDecl->getDeclName();
        const auto& qname = enumDecl->getQualifiedNameAsString();
        int count         = 0;
        for (auto _ : enumDecl->enumerators()) count++;
        std::string macroName = "";
        auto rec = [&](this const auto& self, const DeclContext* c) -> void {
            auto parent = c->getParent();
            if (parent != nullptr && !parent->isTranslationUnit()) {
                self(parent);
            }
            if (c->isNamespace()) {
                auto n = static_cast<const NamespaceDecl*>(c);
                macroName += n->getName(); 
            } else if (c->isRecord()) {
                auto n = static_cast<const CXXRecordDecl*>(c);
                macroName += n->getName();
                auto plist = n->getDescribedTemplateParams();
                if (plist) {
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"
                    for (auto it = plist->begin(); it != plist->end(); ++it) {
                        if (it != plist->end()-1) {
                            macroName += formatv("{}_", (*it)->getName());
                        } else {
                            macroName += formatv("{}", (*it)->getName());
                        }
                    }
#pragma clang diagnostic pop
                }
            }
            macroName += "_";
        };
        auto parent = enumDecl->getParent();
        if (parent != nullptr && !parent->isTranslationUnit()) {
            rec(parent);
        }
        macroName += sname.getAsString();
        //llvm::outs() << macroName;
        ss +=
            formatv("#define REFLG_{3} template<>struct refl::meta<{0}>:EnumType<{0},\"{1}\",\"{0}\">{static "
                    "constexpr std::array<refl::Enumerator<{0}>,{2}>enumerators={{",
                    qname, sname, count, macroName);

        for (int f = 0; const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            if (f++)
                ss += ',';
            ss += formatv("refl::Enumerator<{0}>{{\"{1}\",{0}::{1}}", qname, n);
        }

        ss += formatv(
            "};static constexpr bool valid({0} v)noexcept{{for(const "
            "auto&e:enumerators)if(e.value==v)return true;return "
            "false;}template<refl::e::enum_serializer S>static constexpr std::string_view to_string({0} "
            "v)noexcept{{switch(v){{",
            qname
        );

        int i = 0;
        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return S::serializations[{2}];", qname, n, i++);
        }

        ss += formatv(
            "default:{{assert(false);__builtin_unreachable();}}}"
            "static constexpr std::string_view to_string({0} "
            "v)noexcept{{switch(v){{",
            qname
        );

        i = 0;
        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return enumerators[{2}].name;", qname, n, i++);
        }

        ss += formatv("default:{{assert(false);__builtin_unreachable();}}}"
                      "static constexpr std::string_view "
                      "to_string_safe({0} v)noexcept{{switch(v){{",
                      qname);
        i = 0;
        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return enumerators[{2}].name;", qname, n, i++);
        }

        ss += formatv(
            "default:return{{};}}template <refl::e::enum_serializer S>static constexpr std::string_view "
            "to_string_safe({0} v)noexcept{{switch(v){{",
            qname
        );

        i = 0;
        for (const auto e : enumDecl->enumerators()) {
            const auto& n = e->getName();
            ss += formatv("case {0}::{1}:return S::serializations[{2}];", qname, n, i++);
        }

        ss += formatv(
            "default:return{{};}}static constexpr "
            "std::optional<{0}>from_string(std::string_view "
            "n)noexcept{{for(const auto&e:enumerators)if(e.name==n)return "
            "e.value;return std::nullopt;}"
            "template<refl::e::enum_serializer S> static constexpr "
            "std::optional<{0}>from_string(std::string_view "
            "n)noexcept{{size_t i = 0;for(const auto&e:S::serializations){{"
            "if(e==n)return enumerators[i].value;i++;}return std::nullopt;}"
            "};\n",
            qname
        );
    }
}

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wglobal-constructors"
#pragma clang diagnostic ignored "-Wexit-time-destructors"

// Set up the command line options
static cl::extrahelp CommonHelp(clang::tooling::CommonOptionsParser::HelpMessage);
static cl::OptionCategory ReflToolCategory("refl-tool options");
static cl::opt<std::string> baseFolder("base-path", cl::desc("The common base path for all files."), cl::cat(ReflToolCategory));
static cl::opt<std::string> metaFolder("meta-path", cl::desc("The meta folder where the output files will be written."), cl::cat(ReflToolCategory));
static cl::opt<std::string> CompilationDB("compilation-database", cl::desc("The compilation database."), cl::cat(ReflToolCategory));
static cl::opt<std::string> dependencyOutput("dependency-output", cl::desc("Where to write makefile dependencies of the specified file."), cl::cat(ReflToolCategory));

#pragma clang diagnostic pop

static std::unique_ptr<tooling::CompilationDatabase>
getCompilationDatabase(std::string &ErrorMessage) {
  if (CompilationDB.empty()) {
    llvm::errs() << "The compilation command line must be provided either via "
                    "'-compilation-database'.";
    return nullptr;
  }

    return tooling::JSONCompilationDatabase::loadFromFile(
        CompilationDB, ErrorMessage,
        tooling::JSONCommandLineSyntax::AutoDetect);
}

class SharedStream {
public:
  SharedStream(raw_ostream &OS) : OS(OS) {}
  void applyLocked(llvm::function_ref<void(raw_ostream &OS)> Fn) {
    std::unique_lock<std::mutex> LockGuard(Lock);
    Fn(OS);
    OS.flush();
  }

private:
  std::mutex Lock;
  raw_ostream &OS;
};

class ResourceDirectoryCache {
public:
  /// findResourceDir finds the resource directory relative to the clang
  /// compiler being used in Args, by running it with "-print-resource-dir"
  /// option and cache the results for reuse. \returns resource directory path
  /// associated with the given invocation command or empty string if the
  /// compiler path is NOT an absolute path.
  StringRef findResourceDir(const tooling::CommandLineArguments &Args,
                            bool ClangCLMode) {
    if (Args.size() < 1)
      return "";

    const std::string &ClangBinaryPath = Args[0];
    if (!llvm::sys::path::is_absolute(ClangBinaryPath))
      return "";

    const std::string &ClangBinaryName =
        std::string(llvm::sys::path::filename(ClangBinaryPath));

    std::unique_lock<std::mutex> LockGuard(CacheLock);
    const auto &CachedResourceDir = Cache.find(ClangBinaryPath);
    if (CachedResourceDir != Cache.end())
      return CachedResourceDir->second;

    std::vector<StringRef> PrintResourceDirArgs{ClangBinaryName};
    if (ClangCLMode)
      PrintResourceDirArgs.push_back("/clang:-print-resource-dir");
    else
      PrintResourceDirArgs.push_back("-print-resource-dir");

    llvm::SmallString<64> OutputFile, ErrorFile;
    llvm::sys::fs::createTemporaryFile("print-resource-dir-output",
                                       "" /*no-suffix*/, OutputFile);
    llvm::sys::fs::createTemporaryFile("print-resource-dir-error",
                                       "" /*no-suffix*/, ErrorFile);
    llvm::FileRemover OutputRemover(OutputFile.c_str());
    llvm::FileRemover ErrorRemover(ErrorFile.c_str());
    std::optional<StringRef> Redirects[] = {
        {""}, // Stdin
        OutputFile.str(),
        ErrorFile.str(),
    };
    if (llvm::sys::ExecuteAndWait(ClangBinaryPath, PrintResourceDirArgs, {},
                                  Redirects)) {
      auto ErrorBuf =
          llvm::MemoryBuffer::getFile(ErrorFile.c_str(), /*IsText=*/true);
      llvm::errs() << ErrorBuf.get()->getBuffer();
      return "";
    }

    auto OutputBuf =
        llvm::MemoryBuffer::getFile(OutputFile.c_str(), /*IsText=*/true);
    if (!OutputBuf)
      return "";
    StringRef Output = OutputBuf.get()->getBuffer().rtrim('\n');

    return Cache[ClangBinaryPath] = Output.str();
  }

private:
  std::map<std::string, std::string> Cache;
  std::mutex CacheLock;
};

int main(int argc, const char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  auto ExpectedParser =
      tooling::CommonOptionsParser::create(argc, argv, ReflToolCategory);
  if (!ExpectedParser) {
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }

    using namespace clang::tooling::dependencies;
std::string ErrorMessage;
std::unique_ptr<tooling::CompilationDatabase> Compilations =
      getCompilationDatabase(ErrorMessage);
  if (!Compilations) {
    llvm::errs() << ErrorMessage << "\n";
    return 1;
  }

    if (dependencyOutput.getValue() == "") {
    llvm::errs() << "-dependency-output is mandatory"<< "\n";
    return 1;

    }

  // Expand response files in advance, so that we can "see" all the arguments
  // when adjusting below.
  Compilations = expandResponseFiles(std::move(Compilations),
                                     llvm::vfs::getRealFileSystem());

  Compilations = inferTargetAndDriverMode(std::move(Compilations));

  Compilations = inferToolLocation(std::move(Compilations));

  // The command options are rewritten to run Clang in preprocessor only mode.
  auto AdjustingCompilations =
      std::make_unique<tooling::ArgumentsAdjustingCompilations>(
          std::move(Compilations));
  AdjustingCompilations->appendArgumentsAdjuster(
      [](const tooling::CommandLineArguments &Args,
                          StringRef _ /*FileName*/) {
        std::string LastO;
        bool ClangCLMode = false;
        auto FlagsEnd = llvm::find(Args, "--");
        if (FlagsEnd != Args.begin()) {
          ClangCLMode =
              llvm::sys::path::stem(Args[0]).contains_insensitive("clang-cl") ||
              llvm::is_contained(Args, "--driver-mode=cl");

          // Reverse scan, starting at the end or at the element before "--".
          auto R = std::make_reverse_iterator(FlagsEnd);
          auto E = Args.rend();
          // Don't include Args[0] in the iteration; that's the executable, not
          // an option.
          if (E != R)
            E--;
          for (auto I = R; I != E; ++I) {
            StringRef Arg = *I;
            if (ClangCLMode) {
              // Ignore arguments that are preceded by "-Xclang".
              if ((I + 1) != E && I[1] == "-Xclang")
                continue;
              if (LastO.empty()) {
                // With clang-cl, the output obj file can be specified with
                // "/opath", "/o path", "/Fopath", and the dash counterparts.
                // Also, clang-cl adds ".obj" extension if none is found.
                if ((Arg == "-o" || Arg == "/o") && I != R)
                  LastO = I[-1]; // Next argument (reverse iterator)
                else if (Arg.starts_with("/Fo") || Arg.starts_with("-Fo"))
                  LastO = Arg.drop_front(3).str();
                else if (Arg.starts_with("/o") || Arg.starts_with("-o"))
                  LastO = Arg.drop_front(2).str();

                if (!LastO.empty() && !llvm::sys::path::has_extension(LastO))
                  LastO.append(".obj");
              }
            }
          }
        }
        tooling::CommandLineArguments AdjustedArgs(Args.begin(), FlagsEnd);
        // The clang-cl driver passes "-o -" to the frontend. Inject the real
        // file here to ensure "-MT" can be deduced if need be.
        if (ClangCLMode && !LastO.empty()) {
          AdjustedArgs.push_back("/clang:-o");
          AdjustedArgs.push_back("/clang:" + LastO);
        }

        AdjustedArgs.insert(AdjustedArgs.end(), FlagsEnd, Args.end());
        return AdjustedArgs;
      });

  std::vector<tooling::CompileCommand> Inputs =
      AdjustingCompilations->getAllCompileCommands();

  DependencyScanningService Service(ScanningMode::DependencyDirectivesScan, ScanningOutputFormat::Make, ScanningOptimizations::Default);
    DependencyScanningTool WorkerTool(Service);
    for (auto& it : Inputs) {
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"
        if (fs::equivalent(it.Filename, argv[1])) {
#pragma clang diagnostic pop
            it.CommandLine.push_back("-DREFL_GENERATE");
            auto res = WorkerTool.getDependencyFile(it.CommandLine, it.Directory);
            if (auto E = res.takeError()) {
                auto str = toString(std::move(E));
                if (str != "") llvm::errs() << "Error happened during dependency generation: " << str << "\n";
                break;
            }
            auto p = fs::absolute(fs::path{dependencyOutput.getValue()});
            auto fn = p;
            fn.remove_filename();
            fs::create_directories(fn);
            auto f = std::ofstream{p};
            f << *res << "\n";
            break;
        }
    }



    if (baseFolder.getValue() == "" || metaFolder == "") {
        llvm::errs() << "Both base_path and meta_path arguments are required.\n";
        return 1;
    }

  auto Executor = clang::tooling::createExecutorFromCommandLineArgs(
      argc, argv, ReflToolCategory);

  if (!Executor) {
    llvm::errs() << llvm::toString(Executor.takeError()) << "\n";
    return 1;
  }

    using namespace clang::ast_matchers;
    
    ReflRecordMatchCallback MatchRecordCallback{baseFolder.getValue(), metaFolder.getValue()};
    MyMatchFinder MatchFinder{&MatchRecordCallback};

    auto ReflectedRecordsMatchExpression(cxxRecordDecl(
        anyOf(hasReflectAttr("none"), hasReflectAttr("all"))
    ));
    auto ReflectedEnumMatchExpression(
        enumDecl(anyOf(hasReflectAttr("none"), hasReflectAttr("all")))
    );
    MatchFinder.addMatcher(
        ReflectedRecordsMatchExpression.bind("refl_record"),
        &MatchRecordCallback
    );
    MatchFinder.addMatcher(ReflectedEnumMatchExpression.bind("refl_enum"), &MatchRecordCallback);

  auto Err = Executor->get()->execute(clang::tooling::newFrontendActionFactory(&MatchFinder));
  if (Err) {
    llvm::errs() << llvm::toString(std::move(Err)) << "\n";
  }
  Executor->get()->getToolResults()->forEachResult(
      [](llvm::StringRef key, llvm::StringRef value) {
        llvm::errs() << "----" << key.str() << "\n" << value.str() << "\n";
      });
}
