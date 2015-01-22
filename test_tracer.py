import ast
from tracer import determine_type
from context import add_scope_context, add_variable_context


def test_standpoint():
    source = ast.parse("\n".join([
        "x = 3",
        "y = x",
        "z = foo(y)",
    ]))
    source = add_variable_context(source)
    source = add_scope_context(source)
    call = source.body[2].value
    arg = call.args[0]

    t = determine_type(arg, position=source.body[0])
    assert t == "decltype(3)"


def test_simple_fun():
    source = ast.parse("\n".join([
        "x = 3",
        "y = foo(x)",
    ]))
    source = add_variable_context(source)
    source = add_scope_context(source)
    call = source.body[1].value
    arg = call.args[0]

    t = determine_type(arg)
    assert t == "decltype(x)"


def test_type_number():
    source = ast.parse("3")
    number = source.body[0].value
    t = determine_type(number)
    assert t == "decltype(3)"


def test_fun():
    source = ast.parse("\n".join([
        "x = w",
        "y = foo(x)",
        "z = bar(y)",
    ]))
    source = add_variable_context(source)
    source = add_scope_context(source)
    call = source.body[2].value
    arg = call.args[0]

    t = determine_type(arg, position=source.body[1])
    assert t == "decltype(foo(x))" # buggy though..

