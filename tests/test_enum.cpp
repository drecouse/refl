#include <catch2/catch_test_macros.hpp>
#include <map>
#include <refl/refl.hpp>

enum class [[refl::all]] ScopedEnum {
    eVal1 = 3,
    eVal2 = 5,
    eVal3 = 13
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

namespace n1 {
namespace n2 {

enum [[refl::all]] NamspaceEnum : uint8_t {
    eVal1,
    eVal2,
    eVal3
};

}
} // namespace n1

TEST_CASE("Reflection of normal enum in namespaces is tested", "[namespace_enum]")
{
    namespace n = n1::n2;
    CHECK(refl::e::from_string<n::NamspaceEnum>("eVal1") == n::eVal1);

    CHECK(refl::e::to_string<n::NamspaceEnum>(n::eVal3) == "eVal3");

    CHECK(refl::e::to_string_safe<n::NamspaceEnum>(n::eVal2) == "eVal2");

    CHECK(refl::e::to_string_safe<n::NamspaceEnum>(static_cast<n::NamspaceEnum>(-1)) == "");

    bool called = false;
    refl::with<n::NamspaceEnum>([&called]<class E>() {
        CHECK(E::reflected == true);
        CHECK(std::is_same_v<typename E::type, n::NamspaceEnum> == true);
        CHECK(E::name == "NamspaceEnum");
        CHECK(E::qualified_name == "n1::n2::NamspaceEnum");

        std::map<std::string_view, n::NamspaceEnum> enums;
        for (auto e : E::enumerators) {
            enums[e.name] = e.value;
        }
        CHECK(enums.size() == 3);
        CHECK(enums["eVal1"] == n::NamspaceEnum::eVal1);
        CHECK(enums["eVal2"] == n::NamspaceEnum::eVal2);
        CHECK(enums["eVal3"] == n::NamspaceEnum::eVal3);
        called = true;
    });
    CHECK(called == true);
}

struct Test {
    enum [[refl::all]] InnerEnum {
        eVal1,
        eVal2
    };
};

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

enum class NotReflected {
    eVal1
};

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

