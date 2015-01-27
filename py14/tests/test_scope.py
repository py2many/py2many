import ast
from py14.scope import add_scope_context
from py14.context import add_variable_context


class TestScopeTransformer:
    def test_scope_added(self):
        source = ast.parse("\n".join([
            "def foo():",
            "   return 10",
        ]))
        add_scope_context(source)
        assert isinstance(source.scopes[-1], ast.Module)
        assert isinstance(source.body[0].scopes[-1], ast.FunctionDef)
        assert isinstance(source.body[0].body[0].scopes[-1], ast.FunctionDef)


class TestScopeList:
    def test_find_returns_most_upper_definition(self):
        source = ast.parse("\n".join([
            "x = 1",
            "def foo():",
            "   x = 2",
        ]))
        add_scope_context(source)
        add_variable_context(source)
        definition = source.scopes.find("x")
        assert definition.lineno == 1
