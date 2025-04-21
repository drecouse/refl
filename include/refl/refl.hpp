#pragma once
#include <cassert>
#include <concepts>
#include <optional>
#include <stdexcept>
#include <string_view>
#include <tuple>
#include <type_traits>

// std::get, std::tuple_size, std::tuple_element must be supported
#ifndef REFL_TUPLE
    #define REFL_TUPLE std::tuple
#endif

namespace refl {

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

enum class AccessSpecifier {
    Private,
    Protected,
    Public
};

template <typename B, AccessSpecifier I> struct Base {
    using type                              = B;
    static constexpr AccessSpecifier access = I;
};

template <typename P, cxstring... Names> struct PList {
    using types                                                           = P;
    static constexpr std::array<std::string_view, sizeof...(Names)> names = {
        std::string_view{Names}...
    };
};

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wpadded"
template <typename E>
struct Enumerator {
    std::string_view name;
    E value;
};
#pragma clang diagnostic pop

template <typename T, cxstring N, cxstring UN>
struct EnumType {
    static constexpr bool reflected                  = true;
    using type                                       = T;
    static constexpr std::string_view name           = N;
    static constexpr std::string_view qualified_name = UN;
    // std::array<Enumerator<T>, X> enumerators;
};

template <typename T, cxstring N, cxstring UN, typename B, typename F, typename V, typename C>
struct RecordType {
    static constexpr bool reflected                  = true;
    using type                                       = T;
    static constexpr std::string_view name           = N;
    static constexpr std::string_view qualified_name = UN;
    using base_classes                               = B;
    using functions                                  = F;
    using variables                                  = V;
    using constructors                               = C;
};

template <
    auto P,
    cxstring N,
    cxstring UN,
    cxstring ON,
    bool VIRT,
    AccessSpecifier A,
    typename R,
    typename Params,
    auto... TAGS>
struct Func {
    using type                                       = decltype(P);
    using return_type                                = R;
    using parameters                                 = Params;
    static constexpr auto ptr                        = P;
    static constexpr auto access                     = A;
    static constexpr std::string_view name           = N;
    static constexpr std::string_view full_name      = ON;
    static constexpr std::string_view qualified_name = UN;
    static constexpr const bool is_virtual           = VIRT;
    static constexpr REFL_TUPLE tags                 = {TAGS...};

    static constexpr bool is_instance()
    {
        return std::is_member_function_pointer_v<type>;
    }
};

template <
    auto P,
    cxstring N,
    cxstring UN,
    bool MUT,
    AccessSpecifier A,
    auto... TAGS>
struct Var {
    using type                                       = decltype(P);
    static constexpr auto ptr                        = P;
    static constexpr auto access                     = A;
    static constexpr std::string_view name           = N;
    static constexpr std::string_view qualified_name = UN;
    static constexpr bool is_mutable                 = MUT;
    static constexpr REFL_TUPLE tags                 = {TAGS...};

    static constexpr bool is_instance()
    {
        return std::is_member_object_pointer_v<type>;
    }
};

template <cxstring N, typename T, typename Params, auto... TAGS>
struct Constr {
    using type                             = T;
    using parameters                       = Params;
    using parameter_types                  = typename parameters::types;
    static constexpr std::string_view name = N;
    static constexpr REFL_TUPLE tags       = {TAGS...};

    static constexpr bool is_default()
    {
        return std::tuple_size<parameter_types>() == 0;
    }
    static constexpr bool is_copy()
    {
        if constexpr (std::tuple_size<parameter_types>() == 1) {
            return std::is_same_v<
                const T&, std::tuple_element_t<0, parameter_types>>;
        }
        return false;
    }
    static constexpr bool is_move_copy()
    {
        return std::tuple_size<parameter_types>() == 1 &&
               std::is_same_v<T&&, std::tuple_element_t<0, parameter_types>>;
    }
};

template <typename T>
concept has_reflection = requires() {
    { typename T::_meta{} };
};

template <typename T>
concept meta_type = requires() {
    { typename T::variables{} };
    { typename T::constructors{} };
    { typename T::functions{} };
};

template <typename T>
concept tagged_type = requires() {
    { T::tags };
};

template <typename T> struct meta {
    static constexpr bool reflected = false;
};

template <has_reflection T> struct meta<T> : T::_meta {};

template <typename... T>
concept reflected = (... && meta<T>::reflected);

template <typename... T, typename C>
constexpr void with(C&& c)
{
    if constexpr (refl::reflected<T...>) {
        std::forward<C>(c).template operator()<refl::meta<T>...>();
    } else std::runtime_error{"reflection is not available for this type"};
}

template <typename T, typename F>
constexpr void for_each(F&& func)
{
    auto handler = []<typename T1, typename FUNC1, size_t... I>(
                       FUNC1&& f, std::index_sequence<I...>
                   ) {
        (f.template operator()<std::tuple_element_t<I, T1>>(), ...);
    };
    handler.template operator()<T>(
        std::forward<F>(func),
        std::make_index_sequence<std::tuple_size<T>::value>{}
    );
}

template <meta_type T, typename F>
constexpr void for_each_base_class(F&& func)
{
    for_each<typename T::base_classes>(std::forward<F>(func));
}

template <meta_type T, typename F>
constexpr void for_each_variable(F&& func)
{
    for_each<typename T::variables>(std::forward<F>(func));
}

// also finds variables in bases with at least the specified access A
template <meta_type T, refl::AccessSpecifier A, typename F> constexpr void for_each_variable(F&& func)
{
    for_each<typename T::variable>(func);
    for_each_base_class<T>([&]<typename B>() {
        if (static_cast<int>(B::access) >= static_cast<int>(A)) {
            with<typename B::type>([&]<typename M>() {
                for_each_variable<M, A>(func);
            });
        }
    });
}

template <meta_type T, typename F>
constexpr void for_each_constructor(F&& func)
{
    for_each<typename T::constructors>(std::forward<F>(func));
}

template <meta_type T, typename F>
constexpr void for_each_function(F&& func)
{
    for_each<typename T::functions>(std::forward<F>(func));
}

// also finds functions in bases with at least the specified access A
template <meta_type T, refl::AccessSpecifier A, typename F>
constexpr void for_each_function(F&& func)
{
    for_each<typename T::functions>(func);
    for_each_base_class<T>([&]<typename B>() {
        if (static_cast<int>(B::access) >= static_cast<int>(A)) {
            with<typename B::type>([&]<typename M>() {
                for_each_function<M, A>(func);
            });
        }
    });
}

template <typename T, typename F>
constexpr void for_each_parameter(F&& func)
{
    auto handler = []<typename T1, typename FUNC1, size_t... I>(
                       FUNC1&& f, std::index_sequence<I...>
                   ) {
        (f.template operator()<std::tuple_element_t<I, T1>, I>(T::parameters::names[I]), ...);
    };
    handler.template operator()<typename T::parameters::types>(
        std::forward<F>(func),
        std::make_index_sequence<std::tuple_size<typename T::parameters::types>::value>{}
    );
}

template <tagged_type T, typename TAG, typename F>
constexpr void with_tag(F&& func)
{
    auto handler = []<typename FUNC1, typename T1, size_t... I>(
                       FUNC1&& f, const T1& d, std::index_sequence<I...>
                   ) {
        (
            [](FUNC1&& f1, const T1& d1) {
                if constexpr (std::is_same_v<TAG, std::tuple_element_t<I, T1>>)
                    f1(std::get<I>(d1));
            }(std::forward<FUNC1>(f), d),
            ...
        );
    };
    handler(
        std::forward<F>(func), T::tags,
        std::make_index_sequence<std::tuple_size_v<decltype(T::tags)>>{}
    );
}

namespace detail {

template <tagged_type T, typename TAG> static inline constexpr bool has_tag()
{
    auto handler = []<typename T1, size_t... I>(const T1, std::index_sequence<I...>) {
        return (... || std::is_same_v<TAG, std::tuple_element_t<I, T1>>);
    };
    return handler(
        T::tags,
        std::make_index_sequence<std::tuple_size_v<decltype(T::tags)>>{}
    );
}

} // namespace detail

template <typename T, typename TAG>
concept has_tag = detail::has_tag<T, TAG>();

namespace e {
namespace detail {

template <typename T>
concept c_enum = std::is_enum_v<T>;

}

template <detail::c_enum T>
std::optional<T> from_string(std::string_view name)
{
    if constexpr (reflected<T>) return meta<T>::from_string(name);
    else throw std::runtime_error{"reflection is not available for this enum"};
}
template <detail::c_enum T>
std::string_view to_string(T value)
{
    if constexpr (reflected<T>) return meta<T>::to_string(value);
    else throw std::runtime_error{"reflection is not available for this enum"};
}
template <detail::c_enum T>
std::string_view to_string_safe(T value)
{
    if constexpr (reflected<T>) return meta<T>::to_string_safe(value);
    else throw std::runtime_error{"reflection is not available for this enum"};
}
template <detail::c_enum T>
bool valid(T value)
{
    if constexpr (reflected<T>) return meta<T>::valid(value);
    else throw std::runtime_error{"reflection is not available for this enum"};
}
template <detail::c_enum T, typename F>
    requires std::invocable<F, T, std::string_view>
void for_each(F&& func)
{
    if constexpr (reflected<T>) {
        for (const auto& it : meta<T>::enumerators) { func(it.value, it.name); }
    } else throw std::runtime_error{"reflection is not available for this enum"};
}

} // namespace e

} // namespace refl

