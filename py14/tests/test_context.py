import ast
from py2many.context import add_variable_context, add_list_calls
from py2many.scope import add_scope_context


def parse(*args):
    source = ast.parse("\n".join(args))
    add_scope_context(source)
    add_variable_context(source)
    return source


class TestListCallTransformer:
    def test_call_added(self):
        source = parse("results = []", "results.append(x)")
        add_list_calls(source)
        assert len(source.scopes[-1].vars[0].calls) == 1


class TestVariableTranformer:
    def test_vars_of_if(self):
        source = parse("x = 5", "if True:", "   y = 10", "   x *= y")
        assert len(source.vars) == 1
        assert len(source.body[1].body_vars) == 2

    def test_vars_of_else(self):
        source = parse(
            "x = 5",
            "if True:",
            "    y = 10",
            "    x *= y",
            "else:",
            "    z = 3",
            "    x *= z",
        )
        assert len(source.vars) == 1
        assert len(source.body[1].body_vars) == 2
        assert len(source.body[1].orelse_vars) == 2

    def test_local_vars_of_function(self):
        source = parse(
            "def foo():",
            "   results = []",
            "   x = 3",
            "   z = x",
            "   results.append(x)",
            "   return results",
        )
        assert len(source.vars) == 1
        assert len(source.body[0].vars) == 3

    def test_local_vars_of_function_with_args(self):
        source = parse("def foo(x, y):", "   return x + y")
        assert len(source.vars) == 1
        assert len(source.body[0].vars) == 2

    def test_subscripts_are_ignored(self):
        source = parse("x[0] = 3")
        assert len(source.vars) == 0

    def test_vars_from_loop(self):
        source = parse("newlist = []", "for x in list:", "   newlist.append(x)")
        assert len(source.vars) == 1

    def test_global_vars_of_module(self):
        source = parse(
            "x  = 3",
            "def foo():",
            "   results = []",
            "   results.append(x)",
            "   return results",
        )
        assert len(source.vars) == 2
        assert len(source.body[1].vars) == 1

    def test_vars_inside_loop(self):
        source = parse(
            "def foo():",
            "   results = []",
            "   for x in range(0, 10):",
            "       results.append(x)",
            "   return results",
        )
        assert len(source.vars) == 1
        assert len(source.body[0].body[1].vars) == 1
