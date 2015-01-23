import ast
from tracer import determine_type, catch_value_expression
from context import add_scope_context, add_variable_context, add_list_calls


def parse(lines):
    source = ast.parse("\n".join(lines))
    source = add_variable_context(source)
    source = add_scope_context(source)
    return source


def test_direct_assignment():
    source = parse(["x = 3"])
    x = source.body[0]
    t = determine_type(x)
    assert t == "decltype(3)"


def test_assign_name():
    source = parse([
        "x = 3",
        "y = x",
    ])
    y = source.body[1]
    t = determine_type(y)
    assert t == "decltype(x)"


def test_assign_function():
    source = parse([
        "x = 3",
        "y = foo(x)",
    ])
    y = source.body[1]
    t = determine_type(y)
    assert t == "decltype(foo(x))"


def test_list_assignment_with_default_values():
    source = parse([
        "x = 3",
        "results = [x]",
    ])
    results = source.body[1]
    t = determine_type(results)
    assert t == "std::vector<decltype(x)>"

def test_list_assignment_with_function_call_as_value():
    source = parse([
        "x = 3",
        "results = [foo(x)]",
    ])
    results = source.body[1]
    t = determine_type(results)
    assert t == "std::vector<decltype(foo(x))>"

def test_list_assignment_based_on_later_append():
    source = parse([
        "x = 3",
        "results = []",
        "results.append(x)",
    ])
    add_list_calls(source)
    results = source.body[1]
    t = determine_type(results)
    assert t == "std::vector<decltype(x)>" # bug..

def test_catch_long_expression_chain():
    source = parse([
        "x = 3 * 1",
        "y = x - 5",
        "z = y + 2",
    ])
    z = source.body[2]
    t = catch_value_expression(z)
    assert t == "3 * 1 - 5 + 2"

def test_catch_expression_chain_with_functions():
    source = parse([
        "x = 3 * 1",
        "y = foo(x)",
        "z = y + 2",
    ])
    z = source.body[2]
    t = catch_value_expression(z)
    assert t == "foo(3 * 1) + 2"
