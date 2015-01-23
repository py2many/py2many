from tracer import value_type,value_expr, decltype, is_list
from context import add_scope_context, add_variable_context, add_list_calls
import pytest
import ast


def parse(lines):
    source = ast.parse("\n".join(lines))
    source = add_variable_context(source)
    source = add_scope_context(source)
    return source


class TestValueType:
    def test_direct_assignment(self):
        source = parse(["x = 3"])
        x = source.body[0]
        t = value_type(x)
        assert t == "3"

    def test_assign_name(self):
        source = parse([
            "x = 3",
            "y = x",
        ])
        y = source.body[1]
        t = value_type(y)
        assert t == "x"

    def test_assign_function(self):
        source = parse([
            "x = 3",
            "y = foo(x)",
        ])
        y = source.body[1]
        t = value_type(y)
        assert t == "foo(x)"

    def test_list_assignment_with_default_values(self):
        source = parse([
            "x = 3",
            "results = [x]",
        ])
        results = source.body[1]
        t = value_type(results)
        assert t == "x"

    def test_list_assignment_with_function_call_as_value(self):
        source = parse([
            "x = 3",
            "results = [foo(x)]",
        ])
        results = source.body[1]
        t = value_type(results)
        assert t == "foo(x)"

    def test_list_assignment_based_on_later_append(self):
        source = parse([
            "x = 3",
            "results = []",
            "results.append(x)",
        ])
        add_list_calls(source)
        results = source.body[1]
        t = value_type(results)
        assert t == "3" # bug..

    def test_list_assignment_with_append_unknown_value(self):
        source = parse([
            "results = []",
            "x = 3",
            "results.append(x)",
        ])
        add_list_calls(source)
        results = source.body[0]
        t = value_type(results)
        assert t == "3" # bug..


class TestValueExpr:
    def test_catch_long_expression_chain(self):
        source = parse([
            "x = 3 * 1",
            "y = x - 5",
            "z = y + 2",
        ])
        z = source.body[2]
        t = value_expr(z)
        assert t == "3 * 1 - 5 + 2"

    def test_catch_expression_chain_with_functions(self):
        source = parse([
            "x = 3 * 1",
            "y = foo(x)",
            "z = y + 2",
        ])
        z = source.body[2]
        t = value_expr(z)
        assert t == "foo(3 * 1) + 2"


def test_decltype_normal_var():
    source = parse([
        "x = 3",
        "y = foo(x)",
    ])
    y = source.body[1]
    t = decltype(y)
    assert t == "decltype(foo(x))"


def test_decltype_list_var():
    source = parse([
        "results = []",
        "x = 3",
        "results.append(x)",
    ])
    add_list_calls(source)
    results = source.body[0]
    t = decltype(results)
    assert t == "std::vector<decltype(3)>"


def test_is_list():
    source = parse([
        "list1 = []",
        "list2 = list1",
    ])
    add_list_calls(source)
    list2 = source.body[1]
    assert is_list(list2)
