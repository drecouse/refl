#include <format>
#include <print>
#include <refl/refl.hpp>
#include <sstream>
#include <vector>

struct skip_ser {};

struct [[refl::all]] Inner {
    Inner(std::string n, int v1, int v2)
        : name{n}
        , value1{v1}
        , value2{v2}
        , value3{v1 + v2}
    {
    }
    std::string name;
    int value1;

private:
    int value2; // private values can be also automatically serialized

public:
    // values can be tagged to e.g. skip them during serialization
    // the 'refl_tag' must be spelled out in the source without macros
    // the attribute declaration or the concrete tag can be hidden behind
    // separate macros. C++11 style macros will not work here at the moment.
    __attribute__((refl_tag(skip_ser{}))) long long value3;
};

struct [[refl::all]] Example {
    Example()
        : data{"def", 4, 7}
    {
        for (int i = 0; i < 5; ++i) {
            moreData.emplace_back("more", i, i + 1);
        }
    }
    Inner data;
    std::vector<Inner> moreData;
};

// to differentiate between those types that can be directly printed by our
// underlying mechanism (in our example operator<< and std::ostream)
template <typename T>
concept stream_serializable = requires(std::ostream& os, const T& d) {
    { os << d } -> std::convertible_to<std::ostream&>;
};

// base template for the above case
template <typename T>
struct Serializer {
    static void serialize(const T& t, std::ostream& os)
    {
        // we need this to 'trick' the compiler to
        // accept the code if reflection is not available
        if constexpr (stream_serializable<T>) {
            os << t;
        }
    }
};

// standard containers in general could be handled like this
template <typename T>
struct Serializer<std::vector<T>> {
    static void serialize(const std::vector<T>& vec, std::ostream& os)
    {
        os << "[";
        for (int f = 0; const auto& it : vec) {
            if (f++) os << ",";
            Serializer<T>::serialize(it, os);
        }
        os << "]";
    }
};

// this specialization will be applid to every type that is reflected
template <typename T>
    requires(refl::reflected<T>)
struct Serializer<T> {
    static void serialize(const T& data, std::ostream& os)
    {
        os << "{";
        // access the metadata for type T as type M
        refl::with<T>([&]<typename M>() {
            int f = 0;
            // access each variable as type V
            refl::for_each_variable<M>([&]<typename V>() {
                // check if instance variable and if it was not skipped by the tag
                if constexpr (V::is_instance() && !refl::has_tag<V, skip_ser>) {
                    if (f++) os << ",";
                    os << std::format("{}:", V::name);
                    const auto& d = data.*V::ptr;
                    // recursive call to Serializer to handle the data
                    // (either: basic_type, std::vector or any reflected type)
                    Serializer<std::decay_t<decltype(d)>>::serialize(d, os);
                }
            });
        });
        os << "}";
    }
};

int main()
{
    std::stringstream ss;
    Example ex;
    Serializer<Example>::serialize(ex, ss);
    std::print("{}", ss.str());
}

