from py14.transpiler import transpile
import pytest


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
    assert cpp == (
        "inline auto foo() {\n"
        "return;\n"
        "}"
    )


def test_print_multiple_vars():
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
    assert cpp == (
        "auto counter = 0;\n"
        "counter += 5;\n"
        "counter -= 2;\n"
        "counter *= 2;\n"
        "counter /= 3;"
    )


@pytest.mark.xfail
def test_try_except():
    source = parse(
        "try:",
        "   conn = open_connection()",
        "except ConnectionError:",
        '   print("Could not connect")',
    )
    cpp = transpile(source)
    assert cpp == (
        "try {\n"
        "auto conn = open_connection();"
        "}\n"
        "catch(;\n"
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
    assert cpp == (
        "decltype(true) x;\n"
        "if(true) {\n"
        "x = true;\n"
        "} else {\n"
        "x = false;\n"
        "}\n"
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
    assert cpp == (
        "auto x = 5;\n"
        "if(true) {\n"
        "auto y = 10;\n"
        "x *= y;\n"
        "}"
    )


def test_print_program_args():
    source = parse(
        'if __name__ == "__main__":',
        "    for arg in sys.argv:",
        "       print(arg)",
    )
    cpp = transpile(source)
    assert cpp == (
        "int main(int argc, char ** argv) {\n"
        "py14::sys::argv = std::vector<std::string>(argv, argv + argc);\n"
        "for(auto arg : py14::sys::argv) {\n"
        "std::cout << arg << std::endl;\n"
        "}\n"
        "}"
    )


def test_tuple_swap():
    source = parse(
        "x = 3",
        "y = 1",
        "x, y = y, x",
    )
    cpp = transpile(source)
    assert cpp == ("auto x = 3;\n"
                   "auto y = 1;\n"
                   "std::tie(x, y) = std::make_tuple(y, x);")


def test_assign():
    source = parse(
        "x = 3",
        "x = 1",
    )
    cpp = transpile(source)
    assert cpp == "auto x = 3;\nx = 1;"


def test_function_with_return():
    source = parse(
        "def fun(x):",
        "   return x",
    )
    cpp = transpile(source)
    assert cpp == (
        "template <typename T1>\n"
        "auto fun(T1 x) {\n"
        "return x;\n"
        "}"
    )


def test_void_function():
    source = parse(
        "def test_fun():",
        "   assert True",
    )
    cpp = transpile(source)
    print(cpp)
    assert cpp == (
        "inline void test_fun() {\n"
        "REQUIRE(true);\n"
        "}"
    )


def test_create_catch_test_case():
    source = parse(
        "def test_fun():",
        "   assert True",
    )
    cpp = transpile(source, testing=True)
    assert cpp == (
        '#include "catch.hpp"\n'
        'TEST_CASE("test_fun") {\n'
        "REQUIRE(true);\n"
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
    assert cpp == ("std::vector<decltype(1)> values {};\n"
                   "values.push_back(1);")


def test_map_function():
    source = parse(
        "def map(values, fun):",
        "   results = []",
        "   for v in values:",
        "       results.append(fun(v))",
        "   return results",
    )
    cpp = transpile(source)
    assert cpp == (
        "template <typename T1, typename T2>\n"
        "auto map(T1 values, T2 fun) {\n"
        "std::vector<decltype(fun(std::declval"
        "<typename decltype(values)::value_type>()))> results {};\n"
        "for(auto v : values) {\n"
        "results.push_back(fun(v));\n"
        "}\n"
        "return results;\n"
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
    assert cpp == (
        "template <typename T1>\n"
        "auto sort(T1 seq) {\n"
        "auto L = seq.size();\n"
        "for(auto _ : rangepp::range(L)) {\n"
        "for(auto n : rangepp::range(1, L)) {\n"
        "if(seq[n] < seq[n - 1]) {\n"
        "std::tie(seq[n - 1], seq[n]) = "
        "std::make_tuple(seq[n], seq[n - 1]);\n"
        "}\n"
        "}\n" "}\n"
        "return seq;\n"
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
    assert cpp == (
        "template <typename T1>\n"
        "auto fib(T1 n) {\n"
        "if(n == 1) {\n"
        "return 1;\n"
        "} else {\n"
        "if(n == 0) {\n"
        "return 0;\n"
        "} else {\n"
        "return fib(n - 1) + fib(n - 2);\n"
        "}\n"
        "}\n"
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
    assert cpp == (
        "template <typename T1>\n"
        "auto sort(T1 seq) {\n"
        "auto gap = seq.size();\n"
        "auto swap = true;\n"
        "while (gap > 1||swap) {\n"
        "gap = std::max(1, py14::to_int(gap / 1.25));\n"
        "swap = false;\n"
        "for(auto i : rangepp::range(seq.size() - gap)) {\n"
        "if(seq[i] > seq[i + gap]) {\n"
        "std::tie(seq[i], seq[i + gap]) = "
        "std::make_tuple(seq[i + gap], seq[i]);\n"
        "swap = true;\n"
        "return seq;\n"
        "}\n"
        "}\n"
        "}\n"
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
    assert cpp == (
        "template <typename T1, typename T2, typename T3>\n"
        "auto pdf(T1 x, T2 mean, T3 std_dev) {\n"
        "auto term1 = 1.0 / std::pow(2 * py14::math::pi, 0.5);\n"
        "auto term2 = std::pow(py14::math::e, -1.0 * "
        "std::pow(x - mean, 2.0) / 2.0 * std::pow(std_dev, 2.0));\n"
        "return term1 * term2;\n"
        "}"
    )
