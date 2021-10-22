#include <iostream>

template<int V>
struct Int {
    static constexpr int value = V;
};

template<int V>
struct Arg {
    static constexpr int value = V;
};

template<int N, typename Arg, typename ...Args>
struct GetArg_ : GetArg_<N - 1, Args...> {
};

template<typename Arg, typename ...Args>
struct GetArg_<1, Arg, Args...> {
    using type = Arg;
};

template<int N, typename ...Args>
using GetArg = typename GetArg_<N, Args...>::type;

template<typename T, typename ...Params>
struct Lambda;

template<template<typename ...> typename T, typename ...Params>
struct Lambda<T<Params...> > {
    template<typename ...Args>
    struct apply {
        using type = T<typename Lambda<Params, Args...>::type...>;
    };
};

template<int N, typename ...Args>
struct Lambda<Arg<N>, Args...> {
    using type = GetArg<N, Args...>;
};

template<typename L, typename ...Args>
struct Apply {
    using type = typename L::template apply<Args...>::type;
};

template<typename L, typename ...Args>
using Apply_t = typename Apply<L, Args...>::type;

namespace placeholders {
    using _1 = Arg<1>;
    using _2 = Arg<2>;
    using _3 = Arg<3>;
    // ...
}

// Experiments

using namespace placeholders;

template<typename A1, typename A2>
struct Add {
    static constexpr int value = Int<A1::value + A2::value>::value;
};

template<typename A1>
using twice_template = typename Apply_t<Lambda<Apply<_1, _2, _2> >, Lambda<Add<_1, _2> >, A1>::type;

int main() {
    // Nested templates like `Lambda<Add<Add<_1, _1>, _1> >` would fail
    using twice_lambda = Lambda<Add<_1, _1> >;
    using result1 = Apply_t<twice_lambda, Int<21> >;
    std::cout << result1::value << std::endl;

    // Supports applications within lambda expressions
    using result2 = twice_template<Int<21> >;
    std::cout << result2::value << std::endl;
}
