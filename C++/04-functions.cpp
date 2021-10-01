#include <functional>
#include <type_traits>

using namespace std;

// Auxiliary templates

template<typename, typename = void>
struct has_operator_fc_member
        : false_type {
};

template<typename T>
struct has_operator_fc_member<T, void_t<decltype(&T::operator())> >
        : true_type {
};

template<typename F>
struct function_traits : function_traits<decltype(&F::operator())> {
};

template<typename Ret, typename C, typename ...Args>
struct function_traits<Ret(C::*)(Args...) const> {
    static function<Ret(Args...)> convert(Ret(*f)(Args...)) {
        return f;
    }
};

// Turning callables into std::function<...>s

template<typename Ret, typename ...Args>
auto make_func(Ret(*f)(Args...)) -> function<Ret(Args...)> {
    return f;
}

template<typename F>
auto make_func(F f) {
    return enable_if_t<
            has_operator_fc_member<F>::value,
            function_traits<F>
    >::convert(f);
}

// Experiments

int test_1(int a, int b, int c) { return a + b * c; }

int main() {
    auto test_2 = [](int a, int b, int c) -> int { return a + b * c; };
    auto fun_1 = make_func(test_1);
    auto fun_2 = make_func(test_2);
}
