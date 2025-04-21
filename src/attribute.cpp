#include "clang/AST/ASTContext.h"
#include "clang/Sema/Sema.h"
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/Sema/ParsedAttr.h>

using namespace clang;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"

template <unsigned N> struct cxstring {
    char buf[N + 1]{};
    constexpr cxstring(char const* s)
    {
        for (auto i = 0ull; i != N; ++i) buf[i] = s[i];
    }
    constexpr operator char const*() const noexcept { return buf; }
    constexpr operator std::string_view() const noexcept
    {
        return std::string_view{buf, N};
    }
};
template <unsigned N> cxstring(char const (&)[N]) -> cxstring<N - 1>;

#pragma clang diagnostic pop

template <cxstring SP, cxstring Annotation>
class ReflectClassAttrInfo : public ParsedAttrInfo {
public:
    ReflectClassAttrInfo()
    {
        static constexpr Spelling S[] = {
            {ParsedAttr::AS_CXX11, SP}
        };
        Spellings = S;
        OptArgs   = 0;
    }

    bool diagAppertainsToDecl(Sema& S, const ParsedAttr& Attr, const Decl* D) const override
    {
        if (!isa<RecordDecl>(D) && !isa<EnumDecl>(D)) {
            S.Diag(Attr.getLoc(), diag::warn_attribute_wrong_decl_type)
                << Attr << Attr.isRegularKeywordAttribute()
                << ExpectedTypeOrNamespace; // ??
            return false;
        }
        return true;
    }

    AttrHandling handleDeclAttribute(Sema& S, Decl* D, const ParsedAttr& Attr) const override
    {
        if (Attr.getNumArgs() > 0) {
            unsigned ID = S.getDiagnostics().getCustomDiagID(
                DiagnosticsEngine::Error,
                "'refl::none/all' attributes do not accept arguments"
            );
            S.Diag(Attr.getLoc(), ID);
            return AttributeNotApplied;
        }
        D->addAttr(AnnotateAttr::Create(S.Context, static_cast<const char*>(Annotation), nullptr, 0, Attr.getRange(), AnnotateAttr::CXX11_clang_annotate));
        return AttributeApplied;
    }
};

template <cxstring SP, cxstring Annotation, int NArg>
class ReflectMemberAttrInfo : public ParsedAttrInfo {
public:
    ReflectMemberAttrInfo()
    {
        static constexpr Spelling S[] = {
            {ParsedAttr::AS_CXX11, SP},
            {ParsedAttr::AS_GNU, SP}
        };
        Spellings = S;
        NumArgs   = NArg;
    }

    bool diagAppertainsToDecl(Sema& S, const ParsedAttr& Attr, const Decl* D) const override
    {
        if (isa<VarDecl>(D)) return true;
        if (isa<FieldDecl>(D)) return true;
        if (isa<CXXMethodDecl>(D)) return true;
        S.Diag(Attr.getLoc(), diag::warn_attribute_wrong_decl_type)
            << Attr << Attr.isRegularKeywordAttribute()
            << ExpectedVariableOrFunction; // ??
        return false;
    }

    AttrHandling handleDeclAttribute(Sema& S, Decl* D, const ParsedAttr& Attr) const override
    {
        if (Attr.getNumArgs() != NArg) {
            unsigned ID = S.getDiagnostics().getCustomDiagID(
                DiagnosticsEngine::Error,
                "'refl::include/exclude/tag' attribute does not accept that many arguments"
            );
            S.Diag(Attr.getLoc(), ID);
            return AttributeNotApplied;
        }
        if (Attr.getNumArgs() > 0) {
            SmallVector<Expr*, 16> ArgsBuf;
            for (unsigned i = 0; i < Attr.getNumArgs(); i++) {
                ArgsBuf.push_back(Attr.getArgAsExpr(i));
            }
            D->addAttr(AnnotateAttr::Create(S.Context, static_cast<const char*>(Annotation), ArgsBuf.data(), static_cast<uint32_t>(ArgsBuf.size()), Attr.getRange(), AnnotateAttr::CXX11_clang_annotate));
        } else {
            // Attach an annotate attribute to the Decl.
            D->addAttr(AnnotateAttr::Create(S.Context, static_cast<const char*>(Annotation), nullptr, 0, Attr.getRange(), AnnotateAttr::CXX11_clang_annotate));
        }
        return AttributeApplied;
    }
};

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wglobal-constructors"

static clang::ParsedAttrInfoRegistry::Add<ReflectClassAttrInfo<"refl::none", "refl_none">>
    Z1("reflect_attr_none", "create static reflection information");
static clang::ParsedAttrInfoRegistry::Add<ReflectClassAttrInfo<"refl::all", "refl_all">>
    Z3("reflect_attr_all", "create static reflection information");
static clang::ParsedAttrInfoRegistry::Add<ReflectMemberAttrInfo<"refl::include", "refl_include", 0>>
    Z4("reflect_attr_include", "create static reflection information");
static clang::ParsedAttrInfoRegistry::Add<ReflectMemberAttrInfo<"refl::exclude", "refl_exclude", 0>>
    Z5("reflect_attr_exclude", "create static reflection information");
static clang::ParsedAttrInfoRegistry::Add<ReflectMemberAttrInfo<"refl_tag", "refl_tag", 1>>
    Z6("reflect_attr_tag", "create static reflection information");

#pragma clang diagnostic pop

// TODO: https://github.com/llvm/llvm-project/issues/45791
// CXX11 style '[[]]' attributes cannot have parameters
// in the meantime instead of refl::tag attribute refl_tag is available with one parameter as a GNU style attribute
