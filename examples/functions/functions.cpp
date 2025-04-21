#include <memory>
#include <print>
#include <refl/refl.hpp>

struct [[refl::all]] Example {
    int i = 5;
    void foo(int j) { std::print("foo called with {}\n", j); }
    void bar(double d) { std::print("bar called with {}\n", d); }
    Example operator+(Example that) { return Example{i + that.i}; }
    static void baz(bool b) { std::print("baz called with {}\n", b); }
};

// Base class to build a method call for a member function of T with return type R
template <typename R, typename T>
struct Method {
    virtual ~Method()           = default;
    virtual R call()            = 0;               // call the method
    virtual void set_this(T& t) = 0;               // set this pointer
    template <typename P>
    void set_param(std::string_view name, P param) // set parameter, always copies it
    {
        assert(name != "");
        // the parameter is passed as a void* through a virtual function call
        // to the derived instance.
        set_param_impl(name, reinterpret_cast<void*>(&param));
    }

private:
    virtual void set_param_impl(std::string_view name, void* ptr) = 0;
};

// derived class with deduced types and the concrete pointer
template <auto ptr, typename R, typename T, typename... Args>
struct MethodImpl : Method<R, T> {
    R call() override
    {
        if constexpr (std::is_same_v<void, R>) {
            std::apply(
                [this](auto&&... args) {
                    (object->*ptr)(args...);
                },
                params
            );
        } else {
            return std::apply(
                [this](auto&&... args) {
                    return (object->*ptr)(args...);
                },
                params
            );
        }
    }

    void set_this(T& t) override
    {
        object = &t;
    }

private:
    void set_param_impl(std::string_view name, void* param) override
    {
        // access meta data for type T as M
        refl::with<T>([&]<typename M>() {
            // search for a function F
            refl::for_each_function<M>([&]<typename F>() {
                // that has the same type and value as the specified pointer
                if constexpr (std::is_same_v<decltype(ptr), typename F::type>) {
                    if constexpr (ptr == F::ptr) {
                        // search each parameter of F with type Arg, index I and name n
                        refl::for_each_parameter<F>([&]<typename Arg, int I>(std::string_view n) {
                            if (n == name) { // found the specified parameter
                                // store the value, we are casting back to the same type
                                std::get<I>(params) = std::move(*reinterpret_cast<Arg*>(param));
                            }
                        });
                    }
                }
            });
        });
    }

private:
    std::tuple<Args...> params; // parameter storage
    T* object;                  // this storage
};

// an indirection to deduce the full type of ptr
template <auto ptr, typename R, typename T, typename... Args>
static auto make_method_impl(R (T::*)(Args...))
{
    return std::make_unique<MethodImpl<ptr, R, T, Args...>>();
}

template <auto ptr>
static auto make_method()
{
    return make_method_impl<ptr>(ptr);
}

int main()
{
    // access meta data of Example as M
    refl::with<Example>([]<typename M>() {
        // for each function F in Example
        refl::for_each_function<M>([]<typename F>() {
            Example ex;
            // call the function based on if it is a static or member function
            if constexpr (!F::is_instance()) {
                std::apply(F::ptr, typename F::parameters::types{});
            } else {
                std::apply(
                    [&](auto&&... args) {
                        (ex.*F::ptr)(args...);
                    },
                    typename F::parameters::types{}
                );
            }
        });
    });

    Example ex;
    std::string_view parameterName = "j";
    int parameter                  = 42;

    auto method = make_method<&Example::foo>();
    method->set_this(ex);
    method->set_param(parameterName, parameter);
    method->call();

    auto method2 = make_method<&Example::operator+ >();
    method2->set_this(ex);
    method2->set_param("that", ex);
    ex = method2->call();

    std::print("Result of ex + ex is {}", ex.i);
}
