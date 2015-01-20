#include <iostream>

extern "C" double test_is_100(double);
extern "C" double test_times_2_add_1(double);
extern "C" double test_add_1_times_2(double);
extern "C" double test_call_with_2_arg(double);
extern "C" int32_t test_int32(int32_t);

struct test {
    double (*f)(double);
    double arg;
    double expected;
};

test tests[] = {
    { test_is_100,          0.0, 100.0 },
    { test_is_100,        100.0, 100.0 },
    { test_times_2_add_1,   5.0,  11.0 },
    { test_add_1_times_2,   5.0,  12.0 },
    { test_call_with_2_arg, 9.0,  27.0 },
    0,
};

template <class T>
void assert_equal(T actual, T expected, int test) {
    int b = actual == expected;
    std::cout << (b ? "ok" : "not ok") << " " << test << "\n";
    if (!b) {
        std::cout << "Expected: " << expected << "\n";
        std::cout << "  Result: " << actual << "\n";
    }
}

int main() {
    int i;
    for (i = 0; tests[i].f; ++i) {
        double x = tests[i].f(tests[i].arg);
        assert_equal(x, tests[i].expected, i+1);
    }
    assert_equal(test_int32(4), 104, i+1);
}

