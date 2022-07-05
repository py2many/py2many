import sys
import textwrap

try:
    from py2many.pycpp.transpiler import transpile
except ImportError:
    from pycpp.transpiler import transpile


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
    assert cpp == "#include <catch2/catch_test_macros.hpp>\nREQUIRE(1 == foo(3));"


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
    # Note the args and return type are missing here as this `transpile` wrapper
    # is not the main py2many wrapper, and notably doesnt use PythonMainRewriter.
    assert cpp == parse(
        "void main() {",
        "for(auto arg : std::vector<std::string>(argv, argv + argc)) {",
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
        "#include <catch2/catch_test_macros.hpp>",
        'TEST_CASE("test_fun") {',
        "REQUIRE(true);",
        "}",
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
