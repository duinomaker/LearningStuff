#include <deque>
#include <functional>
#include <iostream>
#include <iterator>

using namespace std;

// Automatic Currying

template<typename Ret, typename Arg>
auto curry_(function<Ret(Arg)> f) {
    return f;
}

template<typename Ret, typename Arg, typename ...Args>
auto curry_(function<Ret(Arg, Args...)> f) {
    return [=](Arg arg) {
        function<Ret(Args...)> rest = [=](Args ...args) -> Ret {
            return f(arg, args...);
        };
        return curry_(rest);
    };
}

template<typename Ret, typename ...Args>
function<Ret(Args...)> make_func(Ret(*f)(Args...)) {
    return f;
}

template<typename F>
auto curry(F f) {
    return curry_(make_func(f));
}

// C#-Func-delegate-like `Func` template

template<typename Arg, typename ...Args>
struct Func_ {
    using type = function<typename Func_<Args...>::type(Arg)>;
};

template<typename Arg>
struct Func_<Arg> {
    using type = Arg;
};

template<typename ...Args>
using Func = typename Func_<Args...>::type;

// List-like operations

template<typename A>
deque<A> prepend(A x, deque<A> l) {
    auto lp = l;
    lp.push_front(x);
    return lp;
}

// Functional utilities

template<typename F, typename G>
auto compose(F f, G g) {
    return [=](auto x) { return f(g(x)); };
}

template<typename A, typename B>
B reduce(Func<A, B, B> f, B r, deque<A> l) {
    if (l.empty()) {
        return r;
    }
    auto rest = l;
    auto first = rest.back();
    rest.pop_back();
    return reduce(f, f(first)(r), rest);
}

template<typename A, typename B>
auto map(Func<A, B> f) {
    return curry(reduce<A, deque<B>>)(compose(curry(prepend<B>), f))({});
}

// Experiments

int main() {
    auto f = [](int x) -> int { return x * 2; };
    auto lst = deque<int>{1, 2, 3, 4, 5};
    auto result = map<int, int>(f)(lst);
    copy(result.begin(), result.end(), ostream_iterator<int>(cout, " "));
    cout << endl;
}
