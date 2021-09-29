#include <iostream>
#include <tuple>

using namespace std;

template<class Func, class Tuple>
class Curried {
private:
    Func _f;
    Tuple _t;

public:
    Curried(Func f, Tuple t) : _f(f), _t(std::move(t)) {}

    template<typename Arg>
    auto operator()(Arg arg) {
        auto t = tuple_cat(_t, make_tuple(arg));
        return Curried<Func, decltype(t)>(_f, t);
    }

    auto eval() {
        return apply(_f, _t);
    }
};

template<class Func>
auto curry(Func f) {
    return Curried<Func, tuple<>>(f, {});
}

int main() {
    auto a = curry([](int a, int b, int c) -> int { return a + b + c; })(1);
    auto b = a(2);
    cout << b(3).eval() << endl;
}
