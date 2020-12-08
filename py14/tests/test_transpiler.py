import sys
import pytest
from py14.transpiler import transpile


def parse(*args):
    return "\n".join(args)


def test_declare():
    source = parse("x = 3")
    cpp = transpile(source)
    assert cpp == "auto x = 3;"


def test_empty_return():
    source = parse(
        "def foo():",
        "   return",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "inline auto foo() {",
        "return;",
        "}",
    )


def test_print_multiple_vars():
    if sys.version_info[0] >= 3:
        source = parse('print(("hi", "there" ))')
    else:
        source = parse('print("hi", "there" )')
    cpp = transpile(source)
    assert cpp == ('std::cout << std::string {"hi"} '
                   '<< std::string {"there"} << std::endl;')


def test_assert():
    source = parse('assert 1 == foo(3)')
    cpp = transpile(source)
    assert cpp == ('REQUIRE(1 == foo(3));')


def test_augmented_assigns_with_counter():
    source = parse(
        "counter = 0",
        "counter += 5",
        "counter -= 2",
        "counter *= 2",
        "counter /= 3",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "auto counter = 0;",
        "counter += 5;",
        "counter -= 2;",
        "counter *= 2;",
        "counter /= 3;"
    )


def test_declare_var_before_if_else_statements():
    source = parse(
        "if True:",
        "   x = True",
        "else:",
        "   x = False",
        "y = x",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "decltype(true) x;",
        "if(true) {",
        "x = true;",
        "} else {",
        "x = false;",
        "}",
        "auto y = x;"
    )


def test_declare_vars_inside_if_as_long_as_possible():
    source = parse(
        "x = 5",
        "if True:",
        "   y = 10",
        "   x *= y",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "auto x = 5;",
        "if(true) {",
        "auto y = 10;",
        "x *= y;",
        "}"
    )


def test_print_program_args():
    source = parse(
        'if __name__ == "__main__":',
        "    for arg in sys.argv:",
        "       print(arg)",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "int main(int argc, char ** argv) {",
        "py14::sys::argv = std::vector<std::string>(argv, argv + argc);",
        "for(auto arg : py14::sys::argv) {",
        "std::cout << arg << std::endl;",
        "}",
        "}"
    )


def test_tuple_swap():
    source = parse(
        "x = 3",
        "y = 1",
        "x, y = y, x",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "auto x = 3;",
        "auto y = 1;",
        "std::tie(x, y) = std::make_tuple(y, x);"
    )


def test_assign():
    source = parse(
        "x = 3",
        "x = 1",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "auto x = 3;",
        "x = 1;"
    )


def test_function_with_return():
    source = parse(
        "def fun(x):",
        "   return x",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "template <typename T1>",
        "auto fun(T1 x) {",
        "return x;",
        "}"
    )


def test_void_function():
    source = parse(
        "def test_fun():",
        "   assert True",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "inline void test_fun() {",
        "REQUIRE(true);",
        "}"
    )


def test_create_catch_test_case():
    source = parse(
        "def test_fun():",
        "   assert True",
    )
    cpp = transpile(source, testing=True)
    assert cpp == parse(
        '#include "catch.hpp"',
        'TEST_CASE("test_fun") {',
        "REQUIRE(true);",
        "}"
    )


def test_list_as_vector():
    source = parse("values = [0, 1, 2, 3]")
    cpp = transpile(source)
    assert cpp == "std::vector<decltype(0)> values {0, 1, 2, 3};"


def test_vector_find_out_type():
    source = parse(
        "values = []",
        "values.append(1)",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "std::vector<decltype(1)> values {};",
        "values.push_back(1);"
    )


def test_map_function():
    source = parse(
        "def map(values, fun):",
        "   results = []",
        "   for v in values:",
        "       results.append(fun(v))",
        "   return results",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "template <typename T1, typename T2>",
        "auto map(T1 values, T2 fun) {",
        "std::vector<decltype(fun(std::declval"
        "<typename decltype(values)::value_type>()))> results {};",
        "for(auto v : values) {",
        "results.push_back(fun(v));",
        "}",
        "return results;",
        "}"
    )


def test_bubble_sort():
    source = parse(
        "def sort(seq):",
        "    L = len(seq)",
        "    for _ in range(L):",
        "        for n in range(1, L):",
        "            if seq[n] < seq[n - 1]:",
        "                seq[n - 1], seq[n] = seq[n], seq[n - 1]",
        "    return seq",
    )
    cpp = transpile(source)
    range_f = "range" if sys.version_info[0] < 3 else "xrange"
    assert cpp == parse(
        "template <typename T1>",
        "auto sort(T1 seq) {",
        "auto L = seq.size();",
        "for(auto _ : rangepp::{0}(L)) {{".format(range_f),
        "for(auto n : rangepp::{0}(1, L)) {{".format(range_f),
        "if(seq[n] < seq[n - 1]) {",
        "std::tie(seq[n - 1], seq[n]) = "
        "std::make_tuple(seq[n], seq[n - 1]);",
        "}",
        "}",
        "}",
        "return seq;",
        "}"
    )


def test_fib():
    source = parse(
        "def fib(n):",
        "    if n == 1:",
        "        return 1",
        "    elif n == 0:",
        "        return 0",
        "    else:",
        "        return fib(n-1) + fib(n-2)",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "template <typename T1>",
        "auto fib(T1 n) {",
        "if(n == 1) {",
        "return 1;",
        "} else {",
        "if(n == 0) {",
        "return 0;",
        "} else {",
        "return fib(n - 1) + fib(n - 2);",
        "}",
        "}",
        "}"
    )


def test_comb_sort():
    source = parse(
        "def sort(seq):",
        "    gap = len(seq)",
        "    swap = True",
        "    while gap > 1 or swap:",
        "        gap = max(1, int(gap / 1.25))",
        "        swap = False",
        "        for i in range(len(seq) - gap):",
        "            if seq[i] > seq[i + gap]:",
        "                seq[i], seq[i + gap] = seq[i + gap], seq[i]",
        "                swap = True",
        "                return seq",
    )
    cpp = transpile(source)
    range_f = "range" if sys.version_info[0] < 3 else "xrange"
    assert cpp == parse(
        "template <typename T1>",
        "auto sort(T1 seq) {",
        "auto gap = seq.size();",
        "auto swap = true;",
        "while (gap > 1||swap) {",
        "gap = std::max(1, py14::to_int(gap / 1.25));",
        "swap = false;",
        "for(auto i : rangepp::{0}(seq.size() - gap)) {{".format(range_f),
        "if(seq[i] > seq[i + gap]) {",
        "std::tie(seq[i], seq[i + gap]) = "
        "std::make_tuple(seq[i + gap], seq[i]);",
        "swap = true;",
        "return seq;",
        "}",
        "}",
        "}",
        "}"
    )


def test_normal_pdf():
    source = parse(
        "def pdf(x, mean, std_dev):",
        "    term1 = 1.0 / ((2 * math.pi) ** 0.5)",
        "    term2 = (math.e ** (-1.0 * (x-mean) ** 2.0 / 2.0",
        "             * (std_dev ** 2.0)))",
        "    return term1 * term2",
    )
    cpp = transpile(source)
    assert cpp == parse(
        "template <typename T1, typename T2, typename T3>",
        "auto pdf(T1 x, T2 mean, T3 std_dev) {",
        "auto term1 = 1.0 / std::pow(2 * py14::math::pi, 0.5);",
        "auto term2 = std::pow(py14::math::e, -1.0 * "
        "std::pow(x - mean, 2.0) / 2.0 * std::pow(std_dev, 2.0));",
        "return term1 * term2;",
        "}"
    )
