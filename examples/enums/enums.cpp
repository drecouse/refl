#include <print>
#include <refl/refl.hpp>

enum class [[refl::all]] TestEnum : int {
    T1 = 5,
    T3 = 7,
    T4 = -1
};

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
    std::print("7 is {}\n", name);

    test = 3;
    e    = static_cast<TestEnum>(test);
    name = refl::e::to_string_safe(e);
    std::print("3 is {}\n", name);

    refl::e::for_each<TestEnum>([](TestEnum v, std::string_view n) {
        std::print("{1} is {0}\n", static_cast<int>(v), n);
    });
}

