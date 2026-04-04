#pragma once

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

enum class ReflSpec { all,
                      none,
                      name,
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
            if (s.starts_with("refl_") && s.substr(5).starts_with("tag"))
                return ReflSpec::tag;
            if (s.starts_with("refl_") && s.substr(5).starts_with("name"))
                return ReflSpec::name;
            if (s.starts_with("refl::") || s.starts_with("refl_")) {
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
#pragma clang diagnostic ignored "-Wunused-function"
static std::string getReflMacroName(const Decl* decl, const SourceManager& SourceManager, ASTContext& Context_)
{
    std::string ret;
    const auto& attrs = decl->getAttrs();
    for (auto a : attrs) {
        if (!strcmp(a->getSpelling(), "annotate")) {
            auto s = static_cast<std::string_view>(Lexer::getSourceText(
                CharSourceRange::getTokenRange(a->getRange()),
                SourceManager, Context_.getLangOpts()
            ));
            if (!s.starts_with("refl_name"))
                continue;
            auto f = s.find_first_of('"');
            auto l = s.find_last_of('"');
            ret = formatv("{0}", s.substr(f + 1, l - f - 1));
            break;
        }
    }
    return ret;
}
#pragma clang diagnostic pop

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
