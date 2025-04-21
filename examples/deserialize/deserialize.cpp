#include <format>
#include <map>
#include <print>
#include <refl/refl.hpp>
#include <sstream>

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
    int value2;

public:
    __attribute__((refl_tag(skip_ser{}))) long long value3;
};

struct [[refl::all]] Example {
    Example()
        : data{"def", 4, 7}
    {
    }
    Inner data;
};

template <typename T>
concept stream_serializable = requires(
    std::ostream& os,
    std::istream& is,
    const T& d,
    T& o
) {
    { os << d } -> std::convertible_to<std::ostream&>;
    { is >> o } -> std::convertible_to<std::istream&>;
};

template <typename T>
struct Serializer {
    static void serialize(const T& t, std::ostream& os)
    {
        if constexpr (stream_serializable<T>) {
            os << t;
        }
    }
    static void deserialize(T& t, std::string_view in)
    {
        if constexpr (stream_serializable<T>) {
            // quite inefficient but good enough for this example
            std::stringstream ss{std::string{in}};
            ss >> t;
        }
    }
};

template <typename T>
    requires(refl::reflected<T>)
struct Serializer<T> {
    static void serialize(const T& data, std::ostream& os)
    {
        os << "{";
        refl::with<T>([&]<typename M>() {
            int f = 0;
            refl::for_each_variable<M>([&]<typename V>() {
                if constexpr (V::is_instance() && !refl::has_tag<V, skip_ser>) {
                    if (f++) os << ",";
                    os << std::format("{}:", V::name);
                    const auto& d = data.*V::ptr;
                    Serializer<std::decay_t<decltype(d)>>::serialize(d, os);
                }
            });
        });
        os << "}";
    }

    static void deserialize(T& data, std::string_view in)
    {
        if (in.front() != '{') throw "{ missing";
        if (in.back() != '}') throw "} missing";
        if (in.size() == 2) return;

        // first collect each name-value pair
        std::map<std::string_view, std::string_view> members;

        const char* begin = &in.front();
        const char* end   = &in.back();
        const char* front = &in[1];
        const char* back  = &in[1];

        // string parsing, no error checking, no white space skipping
        while (front != end) {
            while (*back != ':') {
                back++;
            }
            auto name = in.substr(static_cast<size_t>(front - begin), static_cast<size_t>(back - front));
            back++;
            front = back;
            if (*back == '{') {
                back++;
                int level = 0;
                while (*back != '}' || level != 0) {
                    if (*back == '{') level++;
                    if (*back == '}') level--;
                    back++;
                }
                back++;
                auto value = in.substr(static_cast<size_t>(front - begin), static_cast<size_t>(back - front));
                members.insert(std::make_pair(name, value));
            } else {
                while (*back != ',' && *back != '}') {
                    back++;
                }
                auto value = in.substr(static_cast<size_t>(front - begin), static_cast<size_t>(back - front));
                members.insert(std::make_pair(name, value));
            }
            if (*back == ',') back++;
            front = back;
        }

        refl::with<T>([&]<typename M>() {
            refl::for_each_variable<M>([&]<typename V>() {
                if constexpr (V::is_instance() && !refl::has_tag<V, skip_ser>) {
                    // for each variable we know its type and member pointer here
                    // so we just need to find the corresponding part of the input
                    auto found = members.find(V::name);
                    if (found != members.end()) {
                        auto& d = data.*V::ptr;
                        Serializer<std::decay_t<decltype(d)>>::deserialize(d, found->second);
                    }
                }
            });
        });
    }
};

void test_deserializer();

int main()
{
    std::stringstream ss;
    Example ex;
    ex.data.value1 = 100;
    Serializer<Example>::serialize(ex, ss);
    std::print("{}\n", ss.str());

    Example ex2;
    Serializer<Example>::deserialize(ex2, ss.str());
    std::print("{}, {}, {}\n", ex2.data.name, ex2.data.value1, ex2.data.value3);

    test_deserializer();
}

// The above method "preprocesses" the input recursively so it traverses it multiple times.
// Another approach would be to "preprocess" the class itself by creating a table of
// function pointers that assign a method to parse the input into the corresponding member.
// A skeleton of this is shown here:

template <typename T, typename V>
void deserialize(T& t, std::string_view _)
{
    std::print("{}\n", t.*V::ptr); // dummy print, deserialization could be done here instead
}

void test_deserializer()
{
    typedef void (*fn_deserialize)(Inner&, std::string_view);
    std::map<std::string_view, fn_deserialize> table;
    refl::with<Inner>([&]<typename M>() {
        refl::for_each_variable<M>([&]<typename V>() {
            table[V::name] = &deserialize<typename M::type, V>;
        });
    });

    // test the table
    Inner ex{"sdsd", 5, 3};
    for (auto& it : table) {
        std::print("{}:", it.first);
        it.second(ex, "");
    }
}

