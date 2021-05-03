import sys
import textwrap

from py14.transpiler import transpile


def parse(*args):
    return "\n".join(args)


def test_declare():
    source = parse("x = 3")
    cpp = transpile(source)
    assert cpp == "auto x = 3;"


def test_empty_return():
    source = parse("def foo():", "   return")
    cpp = transpile(source)
    expected = """\
    inline void foo() {
    return;}
    """
    assert cpp == textwrap.dedent(expected)


def test_print_multiple_vars():
    if sys.version_info[0] >= 3:
        source = parse('print(("hi", "there" ))')
    else:
        source = parse('print("hi", "there" )')
    cpp = transpile(source)
    assert cpp == parse(
        'std::cout << std::string{"hi"} << std::string{"there"};',
        "std::cout << std::endl;",
    )


def test_assert():
    source = parse("assert 1 == foo(3)")
    cpp = transpile(source, testing=True)
    assert cpp == '#include "catch.hpp"\nREQUIRE(1 == foo(3));'


def test_augmented_assigns_with_counter():
    source = parse(
        "counter = 0", "counter += 5", "counter -= 2", "counter *= 2", "counter /= 3"
    )
    cpp = transpile(source)
    assert cpp == parse(
        "auto counter = 0;",
        "counter += 5;",
        "counter -= 2;",
        "counter *= 2;",
        "counter /= 3;",
    )


def test_declare_var_before_if_else_statements():
    source = parse("if 10:", "   x = True", "else:", "   x = False", "y = x")
    cpp = transpile(source)
    assert cpp == parse(
        "decltype(true) x;",
        "if(10) {",
        "x = true;",
        "} else {",
        "x = false;",
        "}",
        "auto y = x;",
    )


def test_declare_vars_inside_if_as_long_as_possible():
    source = parse("x = 5", "if 10:", "   y = 10", "   x *= y")
    cpp = transpile(source)
    assert cpp == parse("auto x = 5;", "if(10) {", "auto y = 10;", "x *= y;", "}")


def test_print_program_args():
    source = parse(
        'if __name__ == "__main__":', "    for arg in sys.argv:", "       print(arg)"
    )
    cpp = transpile(source)
    assert cpp == parse(
        "int main(int argc, char ** argv) {",
        "py14::sys::argv = std::vector<std::string>(argv, argv + argc);",
        "for(auto arg : py14::sys::argv) {",
        "std::cout << arg;",
        "std::cout << std::endl;",
        "}}",
        "",
    )


def test_tuple_swap():
    source = parse("x = 3", "y = 1", "x, y = y, x")
    cpp = transpile(source)
    assert cpp == parse(
        "auto x = 3;", "auto y = 1;", "std::tie(x, y) = std::make_tuple(y, x);"
    )


def test_assign():
    source = parse("x = 3", "x = 1")
    cpp = transpile(source)
    assert cpp == parse("auto x = 3;", "x = 1;")


def test_function_with_return():
    source = parse("def fun(x):", "   return x")
    cpp = transpile(source)
    expected = """\
        template <typename T0>auto fun(T0 x) {
        return x;}
    """
    assert cpp == textwrap.dedent(expected)


def test_void_function():
    source = parse("def test_fun():", "   assert True")
    cpp = transpile(source, testing=False)
    expected = """\
        inline void test_fun() {
        assert(true);}
    """
    assert cpp == textwrap.dedent(expected)


def test_create_catch_test_case():
    source = parse("def test_fun():", "   assert True")
    cpp = transpile(source, testing=True)
    assert cpp == parse(
        '#include "catch.hpp"', 'TEST_CASE("test_fun") {', "REQUIRE(true);", "}"
    )


def test_list_as_vector():
    source = parse("values = [0, 1, 2, 3]")
    cpp = transpile(source)
    assert cpp == "std::vector<decltype(0)> values = {0, 1, 2, 3};"


def test_vector_find_out_type():
    source = parse("values = []", "values.append(1)")
    cpp = transpile(source)
    assert cpp == parse("std::vector<decltype(1)> values = {};", "values.push_back(1);")


def test_map_function():
    source = parse(
        "def map(values, fun):",
        "   results = []",
        "   for v in values:",
        "       results.append(fun(v))",
        "   return results",
    )
    cpp = transpile(source)
    expected = """\
        template <typename T0, typename T1>auto map(T0 values, T1 fun) {
        std::vector<decltype(fun(std::declval<typename decltype(values)::value_type>()))> results = {};
        for(auto v : values) {
        results.push_back(fun(v));
        }
        return results;}
    """
    assert cpp == textwrap.dedent(expected)


def test_normal_pdf():
    source = parse(
        "def pdf(x, mean, std_dev):",
        "    term1 = 1.0 / ((2 * math.pi) ** 0.5)",
        "    term2 = (math.e ** (-1.0 * (x-mean) ** 2.0 / 2.0",
        "             * (std_dev ** 2.0)))",
        "    return term1 * term2",
    )
    cpp = transpile(source)
    expected = """\
        template <typename T0, typename T1, typename T2>auto pdf(T0 x, T1 mean, T2 std_dev) {
        auto term1 = 1.0 / (std::pow(2 * (py14::math::pi), 0.5));
        auto term2 = std::pow(py14::math::e, (((-1.0) * (std::pow(x - mean, 2.0))) / 2.0) * (std::pow(std_dev, 2.0)));
        return term1 * term2;}
    """
    assert cpp == parse(textwrap.dedent(expected))
