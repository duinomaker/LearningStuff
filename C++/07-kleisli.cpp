#include <concepts>
#include <iostream>
#include <string>
#include <utility>

template<typename T>
struct mempty;

template<typename T>
T mappend(T, T) = delete;

template<typename M>
concept Monoid = requires(M m) {
    { mempty<M>::value() } -> std::same_as<M>;
    { mappend(m, m) } -> std::same_as<M>;
};

template<Monoid M>
struct Writer {
    template<typename T>
    using type = std::pair<T, M>;
};

auto compose(auto f, auto g) {
    return [=](auto x) {
        auto w1 = g(x);
        auto w2 = f(w1.first);
        return std::make_pair(
                w2.first,
                mappend(w1.second, w2.second));
    };
}

// Experiments

template<>
struct mempty<std::string> {
    static std::string value() {
        return "";
    }
};

template<>
std::string mappend(std::string s1, std::string s2) {
    return s1 + s2;
}

template<typename T>
using Logger = Writer<std::string>::template type<T>;

// The type alias below will also work, but doesn't check if `std::string` is a
// monoid. Try commenting the `mempty` implementation for `std::string` above.

//using Logger = std::pair<T, std::string>;

Logger<int> add_one(int x) {
    return {x + 1, "add_one "};
}

Logger<int> mul_two(int x) {
    return {x * 2, "mul_two "};
}

int main() {
    auto composed = compose(mul_two, add_one);
    auto result = composed(20);
    std::cout << result.first << std::endl;
    std::cout << result.second << std::endl;
}
