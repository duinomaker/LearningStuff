#include <type_traits>

// Basic data types

template<int V>
using Int = std::integral_constant<int, V>;

template<bool V>
using Bool = std::bool_constant<V>;

// List and list operations

struct Nil;

template<typename A, typename B>
struct Cons {
    using car_type = A;
    using cdr_type = B;
};

template<typename T>
using Car = typename T::car_type;

template<typename T>
using Cdr = typename T::cdr_type;

template<int I, int ...Is>
struct IList_ {
    using type = Cons<Int<I>, typename IList_<Is...>::type>;
};

template<int I>
struct IList_<I> {
    using type = Cons<Int<I>, Nil>;
};

template<int ...Is>
using IList = typename IList_<Is...>::type;

template<template<typename> typename F, typename L>
struct Filter_ {
    using type = std::conditional_t<
            F<Car<L> >::value,
            Cons<Car<L>, typename Filter_<F, Cdr<L> >::type>,
            typename Filter_<F, Cdr<L> >::type
    >;
};

template<template<typename> typename F>
struct Filter_<F, Nil> {
    using type = Nil;
};

template<template<typename> typename F, typename L>
using Filter = typename Filter_<F, L>::type;

template<typename L1, typename L2>
struct Concat_ {
    using type = Cons<Car<L1>, typename Concat_<Cdr<L1>, L2>::type>;
};

template<typename L2>
struct Concat_<Nil, L2> {
    using type = L2;
};

template<typename L1, typename L2>
using Concat = typename Concat_<L1, L2>::type;

// Auxiliary templates for pretty-printing the result

template<int ...>
struct P;

template<typename T, typename = void, int ...Is>
struct Pretty_ : Pretty_<T, P<Is...> > {
};

template<typename T, int ...Is>
struct Pretty_<T, P<Is...> > : Pretty_<Cdr<T>, P<Is..., Car<T>::value> > {
};

template<int ...Is>
struct Pretty_<Nil, P<Is...> > {
    using type = P<Is...>;
};

template<typename T>
using Pretty = typename Pretty_<T>::type;

// The quicksort algorithm

template<typename L>
struct QSort_ {
    static constexpr int pivot = Car<L>::value;

    template<typename T>
    using LE = Bool<T::value <= pivot>;

    template<typename T>
    using GT = Bool<pivot < T::value>;

    using l = typename QSort_<Filter<LE, Cdr<L> > >::type;
    using r = typename QSort_<Filter<GT, Cdr<L> > >::type;

    using type = Concat<l, Concat<IList<pivot>, r> >;
};

template<>
struct QSort_<Nil> {
    using type = Nil;
};

template<typename L>
using QSort = typename QSort_<L>::type;

// Experiments

int main() {
    using L = IList<9, 2, 1, 4, 3, 5, 6, 8, 7>;
    using S = QSort<L>;
    Pretty<S> an_error;
}
