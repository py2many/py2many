import ast
from py2many.scope import add_scope_context
from py2many.context import add_variable_context


def parse(*args):
    source = ast.parse("\n".join(args))
    add_scope_context(source)
    return source


class TestScopeTransformer:
    def test_scope_added(self):
        source = parse("def foo():", "   return 10")
        assert isinstance(source.scopes[-1], ast.Module)
        assert isinstance(source.body[0].scopes[-1], ast.FunctionDef)
        assert isinstance(source.body[0].body[0].scopes[-1], ast.FunctionDef)


class TestScopeList:
    def test_find_returns_most_upper_definition(self):
        source = parse("x = 1", "def foo():", "   x = 2")
        add_variable_context(source)
        definition = source.scopes.find("x")
        assert definition.lineno == 1
