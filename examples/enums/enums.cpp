#include <print>
#include <refl/refl.hpp>

enum class [[refl::all]] TestEnum : int {
    T1 = 5,
    T3 = 7,
    T4 = -1
};

struct TestEnumSerializer {
    static constexpr std::array<std::string_view, 3> serializations = {"cus1", "cus2", "cus3"};
};

#define REFL_CLASS TestEnum
#include <refl/generate.inc>

int main()
{
    // namespace refl::e contains helper functions for
    //  - converting enum values to and from string 
    //     (to_string, to_string_safe, from_string)
    //     to_string_safe handles invalid enum values
    //  - checking if an enum value is valid (valid)
    //  - iterating over each enum value (for_each)

    int test              = 7;
    TestEnum e            = static_cast<TestEnum>(test);
    std::string_view name = refl::e::to_string(e);
    std::string_view name2 = refl::e::to_string<TestEnumSerializer>(e);
    std::print("7 is {} or {}\n", name, name2);

    test = 3;
    e    = static_cast<TestEnum>(test);
    name = refl::e::to_string_safe(e);
    name2 = refl::e::to_string_safe<TestEnumSerializer>(e);
    std::print("3 is {} or {}\n", name, name2);

    auto ee = refl::e::from_string<TestEnum, TestEnumSerializer>("cus1");
    std::print("cus1 is {}\n", refl::e::to_string(ee.value()));

    refl::e::for_each<TestEnum>([](TestEnum v, std::string_view n) {
        std::print("{1} is {0}\n", static_cast<int>(v), n);
    });
}

