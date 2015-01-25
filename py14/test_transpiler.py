from transpiler import transpile


def parse(*args):
    return "\n".join(args)


def test_declare():
    source = parse("x = 3")
    cpp = transpile(source)
    assert cpp == "auto x = 3;"


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
    print(cpp)
    assert cpp == ("auto fun = [](auto x) {\n"
                   "return x;\n"
                   "};")


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
        "auto map = [](auto values, auto fun) {\n"
        "std::vector<decltype(fun(std::declval"
        "<typename decltype(values)::value_type>()))> results {};\n"
        "for(auto v : values) {\n"
        "results.push_back(fun(v));\n"
        "}\n"
        "return results;\n"
        "};"
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
        "auto sort = [](auto seq) {\n"
        "auto L = py14::len(seq);\n"
        "for(auto _ : py14::range(L)) {\n"
        "for(auto n : py14::range(1, L)) {\n"
        "if(seq[n] < seq[n - 1]) {\n"
        "std::tie(seq[n - 1], seq[n]) = "
        "std::make_tuple(seq[n], seq[n - 1]);\n"
        "}\n"
        "}\n" "}\n"
        "return seq;\n"
        "};"
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
        "auto sort = [](auto seq) {\n"
        "auto gap = py14::len(seq);\n"
        "auto swap = true;\n"
        "while (gap > 1||swap) {\n"
        "gap = std::max(1, py14::to_int(gap / 1.25));\n"
        "swap = false;\n"
        "for(auto i : py14::range(py14::len(seq) - gap)) {\n"
        "if(seq[i] > seq[i + gap]) {\n"
        "std::tie(seq[i], seq[i + gap]) = "
        "std::make_tuple(seq[i + gap], seq[i]);\n"
        "swap = true;\n"
        "return seq;\n"
        "}\n"
        "}\n"
        "}\n"
        "};"
    )
