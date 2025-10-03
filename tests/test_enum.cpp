#include <catch2/catch_test_macros.hpp>
#include <map>
#include <refl/refl.hpp>

enum class [[refl::all]] ScopedEnum {
    eVal1 = 3,
    eVal2 = 5,
    eVal3 = 13
};

#define REFL_CLASS ScopedEnum
#include <refl/generate.inc>

namespace n1 {
namespace n2 {

enum [[refl::all]] NamespaceEnum : uint8_t {
    eVal1,
    eVal2,
    eVal3
};

}
} // namespace n1
#define REFL_CLASS n1_n2_NamespaceEnum
#include <refl/generate.inc>

struct Test {
    enum [[refl::all]] InnerEnum {
        eVal1,
        eVal2
    };
};
#define REFL_CLASS Test_InnerEnum
#include <refl/generate.inc>

enum class NotReflected {
    eVal1
};

TEST_CASE("Reflection of scoped enum is tested", "[scoped_enum]")
{
    CHECK(refl::e::from_string<ScopedEnum>("eVal1") == ScopedEnum::eVal1);
    CHECK(refl::e::from_string<ScopedEnum>("eVal2") == ScopedEnum::eVal2);
    CHECK(refl::e::from_string<ScopedEnum>("eVal3") == ScopedEnum::eVal3);

    CHECK(refl::e::to_string<ScopedEnum>(ScopedEnum::eVal1) == "eVal1");
    CHECK(refl::e::to_string<ScopedEnum>(ScopedEnum::eVal2) == "eVal2");
    CHECK(refl::e::to_string<ScopedEnum>(ScopedEnum::eVal3) == "eVal3");

    CHECK(refl::e::to_string_safe<ScopedEnum>(ScopedEnum::eVal1) == "eVal1");
    CHECK(refl::e::to_string_safe<ScopedEnum>(ScopedEnum::eVal2) == "eVal2");
    CHECK(refl::e::to_string_safe<ScopedEnum>(ScopedEnum::eVal3) == "eVal3");

    CHECK(refl::e::to_string_safe<ScopedEnum>(static_cast<ScopedEnum>(0)) == "");

    CHECK(refl::e::valid(ScopedEnum::eVal1));
    CHECK_FALSE(refl::e::valid(static_cast<ScopedEnum>(-1)));

    {
        std::map<std::string_view, ScopedEnum> enums;
        refl::e::for_each<ScopedEnum>([&](auto value, auto name) {
            enums[name] = value;
        });

        CHECK(enums.size() == 3);
        CHECK(enums["eVal1"] == ScopedEnum::eVal1);
        CHECK(enums["eVal2"] == ScopedEnum::eVal2);
        CHECK(enums["eVal3"] == ScopedEnum::eVal3);
    }

    bool called = false;
    refl::with<ScopedEnum>([&called]<class E>() {
        CHECK(E::reflected == true);
        CHECK(std::is_same_v<typename E::type, ScopedEnum> == true);
        CHECK(E::name == "ScopedEnum");
        CHECK(E::qualified_name == "ScopedEnum");

        std::map<std::string_view, ScopedEnum> enums;
        for (auto e : E::enumerators) {
            enums[e.name] = e.value;
        }
        CHECK(enums.size() == 3);
        CHECK(enums["eVal1"] == ScopedEnum::eVal1);
        CHECK(enums["eVal2"] == ScopedEnum::eVal2);
        CHECK(enums["eVal3"] == ScopedEnum::eVal3);
        called = true;
    });
    CHECK(called == true);
}

TEST_CASE("Reflection of normal enum in namespaces is tested", "[namespace_enum]")
{
    namespace n = n1::n2;
    CHECK(refl::e::from_string<n::NamespaceEnum>("eVal1") == n::eVal1);

    CHECK(refl::e::to_string<n::NamespaceEnum>(n::eVal3) == "eVal3");

    CHECK(refl::e::to_string_safe<n::NamespaceEnum>(n::eVal2) == "eVal2");

    CHECK(refl::e::to_string_safe<n::NamespaceEnum>(static_cast<n::NamespaceEnum>(-1)) == "");

    bool called = false;
    refl::with<n::NamespaceEnum>([&called]<class E>() {
        CHECK(E::reflected == true);
        CHECK(std::is_same_v<typename E::type, n::NamespaceEnum> == true);
        CHECK(E::name == "NamespaceEnum");
        CHECK(E::qualified_name == "n1::n2::NamespaceEnum");

        std::map<std::string_view, n::NamespaceEnum> enums;
        for (auto e : E::enumerators) {
            enums[e.name] = e.value;
        }
        CHECK(enums.size() == 3);
        CHECK(enums["eVal1"] == n::NamespaceEnum::eVal1);
        CHECK(enums["eVal2"] == n::NamespaceEnum::eVal2);
        CHECK(enums["eVal3"] == n::NamespaceEnum::eVal3);
        called = true;
    });
    CHECK(called == true);
}

TEST_CASE("Reflection of enum inside class is tested", "[inner_enum]")
{
    bool called = false;
    refl::with<Test::InnerEnum>([&called]<class E>() {
        CHECK(E::reflected == true);
        CHECK(std::is_same_v<typename E::type, Test::InnerEnum> == true);
        CHECK(E::name == "InnerEnum");
        CHECK(E::qualified_name == "Test::InnerEnum");
        called = true;
    });
    CHECK(called == true);
}

#include <catch2/matchers/catch_matchers.hpp>

TEST_CASE("Not reflected enum is tested", "[not_reflected_enum]")
{
    bool called = false;
    refl::with<NotReflected>([&called]<class E>() {
        called = true;
    });
    CHECK(called == false);

    CHECK_THROWS_WITH(refl::e::for_each<NotReflected>([](auto, auto) {}), "reflection is not available for this enum");
}

