import ast
from context import add_variable_context, add_scopes


def test_vars_of_if():
    source = ast.parse("""
x = 5
if True:
    y = 10
    x *= y""")
    add_variable_context(source)
    assert len(source.vars) == 1
    assert len(source.body[1].vars) == 1


def test_vars_of_else():
    source = ast.parse("""
x = 5
if True:
    y = 10
    x *= y
else:
    z = 3
    x *= z""")
    add_variable_context(source)
    assert len(source.vars) == 1
    assert len(source.body[1].vars) == 2  # This is a bug...


def test_scope_added():
    source = ast.parse("""
def foo():
    return 10""")
    add_scopes(source)
    assert isinstance(source.body[0].body[0].scope, ast.FunctionDef)


def test_local_vars_of_function():
    source = ast.parse("""
def foo():
    results = []
    x = 3
    z = x
    results.append(x)
    return results""")
    add_variable_context(source)
    assert len(source.vars) == 0
    assert len(source.body[0].vars) == 3


def test_local_vars_of_function_with_args():
    source = ast.parse("""
def foo(x, y):
    return x + y""")
    add_variable_context(source)
    assert len(source.vars) == 0
    assert len(source.body[0].vars) == 2


def test_vars_from_loop():
    source = ast.parse("""
newlist = []
for x in list:
    newlist.append(x)""")
    add_variable_context(source)
    assert len(source.vars) == 1


def test_global_vars_of_module():
    source = ast.parse("""
x  = 3
def foo():
    results = []
    results.append(x)
    return results""")
    add_variable_context(source)
    assert len(source.vars) == 1
    assert len(source.body[1].vars) == 1


def test_vars_inside_loop():
    source = ast.parse("""
def foo():
    results = []
    for x in range(0, 10):
        results.append(x)
    return results""")
    add_variable_context(source)
    assert len(source.vars) == 0
    assert len(source.body[0].body[1].vars) == 1
