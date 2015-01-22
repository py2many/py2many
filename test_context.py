import ast
from context import add_variable_context, add_scope_context


class TestScopeTransformer:
    def test_scope_added(self):
        source = ast.parse("\n".join([
            "def foo():",
            "   return 10",
        ]))
        add_scope_context(source)
        assert isinstance(source.scope, ast.Module)
        assert isinstance(source.body[0].scope, ast.FunctionDef)
        assert isinstance(source.body[0].body[0].scope, ast.FunctionDef)


class TestVariableTranformer:
    def test_vars_of_if(self):
        source = ast.parse("\n".join([
            "x = 5",
            "if True:",
            "   y = 10",
            "   x *= y",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 1
        assert len(source.body[1].body_vars) == 1

    def test_vars_of_else(self):
        source = ast.parse("\n".join([
            "x = 5",
            "if True:",
            "    y = 10",
            "    x *= y",
            "else:",
            "    z = 3",
            "    x *= z",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 1
        assert len(source.body[1].body_vars) == 1
        assert len(source.body[1].orelse_vars) == 1

    def test_local_vars_of_function(self):
        source = ast.parse("\n".join([
            "def foo():",
            "   results = []",
            "   x = 3",
            "   z = x",
            "   results.append(x)",
            "   return results",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 0
        assert len(source.body[0].vars) == 3

    def test_local_vars_of_function_with_args(self):
        source = ast.parse("\n".join([
            "def foo(x, y):",
            "   return x + y",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 0
        assert len(source.body[0].vars) == 2

    def test_vars_from_loop(self):
        source = ast.parse("\n".join([
            "newlist = []",
            "for x in list:",
            "   newlist.append(x)",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 1

    def test_global_vars_of_module(self):
        source = ast.parse("\n".join([
            "x  = 3",
            "def foo():",
            "   results = []",
            "   results.append(x)",
            "   return results",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 1
        assert len(source.body[1].vars) == 1

    def test_vars_inside_loop(self):
        source = ast.parse("\n".join([
            "def foo():",
            "   results = []",
            "   for x in range(0, 10):",
            "       results.append(x)",
            "   return results",
        ]))
        add_variable_context(source)
        assert len(source.vars) == 0
        assert len(source.body[0].body[1].vars) == 1
