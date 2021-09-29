#include <functional>
#include <iostream>
#include <optional>
#include <string>

using namespace std;

template<template<typename> class F, class A, class B>
struct Functor {
    static F<B> fmap(function<B(A)>, F<A>);
};

/* The Maybe Functor */

template<class A, class B>
struct Functor<optional, A, B> {
    static optional<B> fmap(function<B(A)> f, optional<A> v) {
        if (v.has_value()) {
            return {f(v.value())};
        }
        return {};
    }
};

/* The Reader Functor */

template<class R>
struct Reader {
    template<class S>
    using type = function<S(R)>;
};

template<class S>
using StrReader = Reader<string>::type<S>;

template<class A, class B>
struct Functor<StrReader, A, B> {
    static StrReader<B> fmap(function<B(A)> f, StrReader<A> v) {
        return [=](string s) -> B { return f(v(s)); };
    }
};

/* Experiments */

int inc(int v) {
    return v + 1;
}

int read(string s) {
    return stoi(s);
}

int main() {
    auto a = optional<int>(42);
    auto b = Functor<optional, int, int>::fmap(inc, a);

    if (b.has_value()) {
        cout << "Just " << b.value() << endl;
    } else {
        cout << "Nothing" << endl;
    }

    auto inc_reader = Functor<StrReader, int, int>::fmap(inc, read);
    cout << inc_reader("42") << endl;
}
