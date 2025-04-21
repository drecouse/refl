#include <catch2/catch_test_macros.hpp>
#include <refl/refl.hpp>

struct NotReflected {
    int val;
};

TEST_CASE("Testing not reflected class", "[not_reflected]")
{
    bool enter = false;
    refl::with<NotReflected>([&enter]<class M>() {
        enter = true;
    });
    CHECK(enter == false);
}

namespace n1 {

struct [[refl::none]] TestingBasics {
    int val = 42;

    class [[refl::all]] Inner {};
};

} // namespace n1


TEST_CASE("Testing basics", "[basics]")
{
    refl::with<n1::TestingBasics>([]<class M>() {
        CHECK(M::name == "TestingBasics");
        CHECK(M::qualified_name == "n1::TestingBasics");

        CHECK(std::is_same_v<n1::TestingBasics, typename M::type> == true);
        typename M::type b;
        CHECK(b.val == 42);
    });

    refl::with<n1::TestingBasics::Inner>([]<class M>() {
        CHECK(M::qualified_name == "n1::TestingBasics::Inner");
    });
}

class [[refl::all]] Members {
    int privateMember = 5;

public:
    float publicMember        = 42.0;
    mutable int mutableMember = 0;
    int getMember() const
    {
        return privateMember;
    }
};

TEST_CASE("Testing member access", "[members]")
{
    Members m;
    REQUIRE(m.getMember() == 5);
    REQUIRE(m.publicMember == 42.0f);

    int member = 0;

    // inspecting functions and variables
    // iterating over variables and functions
    refl::with<Members>([&]<class M>() {
        // modifying private and public values
        refl::for_each_variable<M>([&]<class VAR>() {
            if constexpr (VAR::name == "privateMember") {
                CHECK(VAR::access == refl::AccessSpecifier::Private);
                CHECK(VAR::qualified_name == "Members::privateMember");
                CHECK(VAR::is_mutable == false);
                m.*VAR::ptr = 6;
            } else if constexpr (VAR::name == "publicMember") {
                CHECK(VAR::access == refl::AccessSpecifier::Public);
                CHECK(VAR::qualified_name == "Members::publicMember");
                CHECK(VAR::is_mutable == false);
                m.*VAR::ptr = 43;
            } else if constexpr (VAR::name == "mutableMember") {
                CHECK(VAR::is_mutable == true);
            }
        });

        // calling functions
        refl::for_each_function<M>([&]<class FUNC>() {
            if constexpr (FUNC::name == "getMember") {
                CHECK(FUNC::access == refl::AccessSpecifier::Public);
                CHECK(FUNC::qualified_name == "Members::getMember");
                CHECK(FUNC::full_name == "getMember()const");
                CHECK(std::is_same_v<typename FUNC::return_type, int> == true);
                member = (m.*FUNC::ptr)();
            }
        });
    });

    CHECK(m.getMember() == 6);
    CHECK(m.publicMember == 43.f);
    CHECK(member == 6);
}

struct [[refl::all]] Overloads {
    int load()
    {
        return 0;
    }
    int load(int a, int b) &
    {
        return a + b;
    }
    int load(float)
    {
        return 1;
    }
    float load(double)
    {
        return 2.0;
    }
    int load(int a, int b) const&
    {
        return a - b;
    }
    int load(int a, int b) &&
    {
        return a * b;
    }
    int load(int a, int b) const volatile&
    {
        return a * b + b;
    }
    int load(int a, int b) volatile
    {
        return a * a + b;
    }
    bool load(bool b)
    {
        return !b;
    }
};

#include <set>

TEST_CASE("Testing overloads", "[overloads]")
{
    // all has unique name
    std::set<std::string_view> overloadNames;
    refl::with<Overloads>([&]<class M>() {
        refl::for_each_function<M>([&]<class F>() {
            if constexpr (F::name == "load") overloadNames.insert(F::full_name);
        });
    });
    CHECK(overloadNames.size() == 9);
}

// template classes work
template <typename T>
struct [[refl::all]] TemplateTest {
    // template functions are not reflected
    template <typename C>
    void tfunc1()
    {
    }

    template <typename C2>
    void tfunc2(C2)
    {
    }

    template <typename C2>
    void tfunc3(C2)
    {
    }

    // TODO:full function template specializations must be excluded
    template <> [[refl::exclude]] void tfunc2<int>(int) {}

    // workaround: explicitly instantiate it by wrapping it into a regular function
    void rfunc2(int a) { tfunc2(a); }
    void rfunc2(float a) { tfunc2(a); }

    // or just an overload over the template name
    void tfunc3(bool b) { tfunc2<bool>(b); }

    void func1(T) {}
};

// explicit template instantiation also works
using TempDouble = TemplateTest<double>;

// specializiation must be again reflected
template <>
struct TemplateTest<float> {
    void func2() {}
};

template <>
struct [[refl::none]] TemplateTest<bool> {
    void func2() {}
};

TEST_CASE("Testing templates", "[template]")
{
    bool tfunc1Found = false, tfunc2Found = false, func1Found = false, tfunc3Found = false;
    int rFunc2Found = 0;
    refl::with<TemplateTest<int>>([&]<typename M>() {
        refl::for_each_function<M>([&]<typename F>() {
            if constexpr (F::name == "tfunc1") {
                tfunc1Found = true;
            } else if constexpr (F::name == "tfunc2") {
                tfunc2Found = true;
            } else if constexpr (F::name == "tfunc3") {
                tfunc3Found = true;
            } else if constexpr (F::name == "func1") {
                func1Found = true;
            } else if constexpr (F::name == "rfunc2") {
                rFunc2Found++;
            }
        });
    });

    CHECK(tfunc1Found == false);
    CHECK(tfunc2Found == false);
    CHECK(tfunc3Found == true);
    CHECK(func1Found == true);
    CHECK(rFunc2Found == 2);

    tfunc1Found = false;
    tfunc2Found = false;
    func1Found  = false;
    refl::with<TemplateTest<double>>([&]<typename M>() {
        refl::for_each_function<M>([&]<typename F>() {
            if constexpr (F::name == "tfunc1") {
                tfunc1Found = true;
            } else if constexpr (F::name == "tfunc2") {
                tfunc2Found = true;
            } else if constexpr (F::name == "func1") {
                func1Found = true;
            }
        });
    });

    CHECK(tfunc1Found == false);
    CHECK(tfunc2Found == false);
    CHECK(func1Found == true);

    bool reflected = false;
    refl::with<TemplateTest<float>>([&]() {
        reflected = true;
    });

    CHECK(reflected == false);

    reflected = false;
    refl::with<TemplateTest<bool>>([&]<typename M>() {
        reflected = true;
    });

    CHECK(reflected == true);
}

struct [[refl::all]] Constructors {
    Constructors() {}
    Constructors(const Constructors&) {}
    Constructors(Constructors&&) {}
    explicit Constructors(int) {}
    Constructors(bool) {}
    Constructors(int, double) {}

    // templates are not reflected
    template <typename T>
    Constructors(T)
    {
    }
};

TEST_CASE("Testing constructors", "[constructors]")
{
    std::string defName, copyName, moveName;
    refl::with<Constructors>([&]<typename M>() {
        CHECK(std::tuple_size_v<typename M::constructors> == 6);

        refl::for_each_constructor<M>([&]<typename C>() {
            if constexpr (C::is_default()) {
                defName = C::name;
            } else if constexpr (C::is_copy()) {
                copyName = C::name;
            } else if constexpr (C::is_move_copy()) {
                moveName = C::name;
            }
        });
    });

    CHECK(defName == "Constructors()");
    CHECK(copyName == "Constructors(const Constructors &)");
    CHECK(moveName == "Constructors(Constructors &&)");
}

struct [[refl::all]] Statics {
    inline static int test = 5;

    static int foo()
    {
        test = 7;
        return test;
    }
};

TEST_CASE("Testing static variables and functions", "[static]")
{
    int oldval = 0, newval = 0;
    refl::with<Statics>([&]<typename M>() {
        refl::for_each_variable<M>([&]<typename V>() {
            if constexpr (!V::is_instance()) {
                oldval = *V::ptr;
            }
        });

        refl::for_each_function<M>([&]<typename V>() {
            if constexpr (!V::is_instance()) {
                newval = V::ptr();
            }
        });
    });

    CHECK(oldval == 5);
    CHECK(newval == 7);
}

class [[refl::all]] All {
public:
    [[refl::exclude]] int a, b;
    int c;
    [[refl::exclude]] All() = default;
};

struct [[refl::none]] None {
    [[refl::include]] int a, b;
    int c;
};

struct Tag {
    int i;
};

// TODO: this does not work because the 'refl_tag(Tag{I})' part must spell out directly in the source
// #define TAG(I) __attribute__((refl_tag(Tag{I})))

struct [[refl::none]] Tags {
    __attribute__((refl_tag(Tag{3}))) bool a;
    [[refl::include]] bool b;
    __attribute__((refl_tag(Tag{5}))) void foo() {}
    __attribute__((refl_tag(Tag{7}))) __attribute__((refl_tag(refl::cxstring{"seven"}))) Tags() = default;
};

TEST_CASE("Attribute testing", "[attributes]")
{
    refl::with<All>([]<typename M>() {
        CHECK(std::tuple_size_v<typename M::variables> == 1);
        CHECK(std::tuple_size_v<typename M::constructors> == 0);
    });

    refl::with<None>([]<typename M>() {
        CHECK(std::tuple_size_v<typename M::variables> == 2);
    });

    refl::with<Tags>([]<typename M>() {
        CHECK(refl::has_tag<std::tuple_element_t<0, typename M::constructors>, Tag> == true);
        int tag     = 0;
        bool bFound = false;
        refl::for_each_variable<M>([&]<typename V>() {
            if constexpr (V::name == "a") {
                refl::with_tag<V, Tag>([&](auto t) {
                    tag = t.i;
                });
            } else if constexpr (V::name == "b") {
                bFound = true;
            }
        });
        CHECK(bFound == true);
        CHECK(tag == 3);
        refl::with_tag<std::tuple_element_t<0, typename M::functions>, Tag>([&](auto t) {
            tag = t.i;
        });
        CHECK(tag == 5);
    });
}

struct [[refl::all]] Operators {
    Operators& operator=(const Operators&) { return *this; }
    Operators& operator-=(const Operators&) { return *this; }
    Operators operator+(const Operators&) { return {}; }
    void operator++() {}
    operator bool() { return true; }
    explicit operator const char*() { return ""; }
    Operators* operator*() { return this; }
    int operator<=>(const Operators&) { return 0; }
};

TEST_CASE("Testing operators", "[operators]")
{
    std::set<std::string_view> names, fullNames;
    refl::with<Operators>([&]<class M>() {
        CHECK(std::tuple_size_v<typename M::functions> == 8);
        refl::for_each_function<M>([&]<class F>() {
            names.insert(F::name);
            fullNames.insert(F::full_name);
        });
    });

    CHECK(names.contains("operator=") == true);
    CHECK(names.contains("operator-=") == true);
    CHECK(names.contains("operator+") == true);
    CHECK(names.contains("operator++") == true);
    CHECK(names.contains("operator bool") == true);
    CHECK(names.contains("operator const char *") == true);
    CHECK(names.contains("operator<=>") == true);
    CHECK(names.contains("operator*") == true);

    CHECK(fullNames.contains("operator=(const Operators &)") == true);
    CHECK(fullNames.contains("operator-=(const Operators &)") == true);
    CHECK(fullNames.contains("operator+(const Operators &)") == true);
    CHECK(fullNames.contains("operator++()") == true);
    CHECK(fullNames.contains("operator bool()") == true);
    CHECK(fullNames.contains("operator const char *()") == true);
    CHECK(fullNames.contains("operator<=>(const Operators &)") == true);
    CHECK(fullNames.contains("operator*()") == true);
}

struct [[refl::all]] PrivateBase {
    void bar() {}
};
struct [[refl::all]] ProtectedBase {};
struct [[refl::all]] PublicBase {
    virtual void foo() {}
    virtual void baz() {}
    virtual void notOverriden() {}
    virtual ~PublicBase() = default;
};
struct [[refl::all]] PublicVirtualBase {};

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Winconsistent-missing-override"
#pragma clang diagnostic ignored "-Wsuggest-override"

struct [[refl::all]] Derived
    : private PrivateBase
    , protected ProtectedBase
    , public PublicBase
    , virtual public PublicVirtualBase {
    void bar() {}
    void foo() override {}
    void baz() {}
};

#pragma clang diagnostic pop

TEST_CASE("Testing inheritance", "[inheritance]")
{
    std::set<std::string_view> priv, prot, pub; // TODO: C++26 , virt;
    int nonVirt = 0, virtFunc = 0, allPubFunc = 0, allPrivFunc;
    refl::with<Derived>([&]<typename M>() {
        refl::for_each_base_class<M>([&]<class B>() {
            refl::with<typename B::type>([&]<class N>() {
                switch (B::access) {
                case refl::AccessSpecifier::Private:   priv.insert(N::name); break;
                case refl::AccessSpecifier::Protected: prot.insert(N::name); break;
                case refl::AccessSpecifier::Public:    pub.insert(N::name); break;
                default: assert(false);
                }
                // TODO: C++26
                // if (std::is_virtual_base_of_v<typename N::type, Derived>) {
                //    virt.insert(N::name);
                // }
            });
        });

        refl::for_each_function<M, refl::AccessSpecifier::Public>([&]<class F>() {
            allPubFunc++;
        });

        refl::for_each_function<M, refl::AccessSpecifier::Private>([&]<class F>() {
            allPrivFunc++;
        });

        refl::for_each_function<M>([&]<class F>() {
            if (F::is_virtual) virtFunc++;
            else nonVirt++;
        });
    });

    CHECK(nonVirt == 1);
    CHECK(virtFunc == 2);
    CHECK(priv.contains("PrivateBase"));
    CHECK(pub.contains("PublicBase"));
    CHECK(pub.contains("PublicVirtualBase"));
    CHECK(prot.contains("ProtectedBase"));
    CHECK(allPubFunc == 6);
    CHECK(allPrivFunc == 7);
    // CHECK(virt.contains("PublicVirtualBase"));
}

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"

struct [[refl::all]] ParamName {
    void foo(int bar, bool baz) {}
    ParamName(double foo) {}
};

#pragma clang diagnostic pop

TEST_CASE("Testing parameter names", "[parameter_names]")
{
    std::set<std::string_view> names;
    refl::with<ParamName>([&]<typename M>() {
        refl::for_each_function<M>([&]<typename F>() {
            for (auto it : F::parameters::names) {
                names.insert(it);
            }
        });

        refl::for_each_constructor<M>([&]<typename C>() {
            for (auto it : C::parameters::names) {
                names.insert(it);
            }
        });
    });

    CHECK(names.contains("bar"));
    CHECK(names.contains("baz"));
    CHECK(names.contains("foo"));
    CHECK(names.size() == 3);
}

