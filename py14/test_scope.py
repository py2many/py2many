import ast
from scope import add_scope_context


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
