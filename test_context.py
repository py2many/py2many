import ast
from context import add_variable_context


def test_local_vars_of_function():
    source = ast.parse("""
def foo():
    results = []
    x = 3
    z = x
    results.append(x)
    return results""")
    add_variable_context(source)
    assert len(source.context) == 0
    assert len(source.body[0].context) == 3


def test_local_vars_of_function_with_args():
    source = ast.parse("""
def foo(x, y):
    return x + y""")
    add_variable_context(source)
    assert len(source.context) == 0
    assert len(source.body[0].context) == 2


def test_global_vars_of_module():
    source = ast.parse("""
x  = 3
def foo():
    results = []
    results.append(x)
    return results""")
    add_variable_context(source)
    assert len(source.context) == 1
    assert len(source.body[1].context) == 1
