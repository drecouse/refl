#include <memory>
#include <print>
#include <refl/refl.hpp>

template <typename T, typename R> struct factory_impl;
template <typename T, typename... Args>
struct factory_impl<T, REFL_TUPLE<Args...>> {
    static std::unique_ptr<T> call(Args&&... args)
    {
        return std::make_unique<T>(std::forward<Args>(args)...);
    }
};

template <typename T>
struct factory : factory_impl<typename T::type, typename T::parameter_types> {};

struct [[refl::all]] Example {
    Example()
    {
        std::print("Constructed\n");
    }
    Example(int a, double b)
    {
        std::print("Constructed: {0} {1}\n", a, b);
    }
};

int main()
{
    // access meta data for Example as M
    refl::with<Example>([]<typename M>() {
        // iterate over each constructor (including move and copy)
        refl::for_each_constructor<M>([]<typename C>() {
            // a function pointer can be obtained here through factory
            if constexpr (std::tuple_size_v<typename C::parameter_types> == 0) {
                auto _ = factory<C>::call();
            } else {
                auto _ = factory<C>::call(1, 3.14);
            }
        });
    });
}

