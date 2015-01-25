import ast
from analysis import FunctionTransformer, CalledWithTransformer
from scope import add_scope_context
from context import add_variable_context


def parse(*args):
    source = ast.parse("\n".join(args))
    add_scope_context(source)
    add_variable_context(source)
    return source


class TestFunctionTransformer:
    def test_nested_functions(self):
        source = parse(
            "def foo():",
            "   def bar():",
            "       def gib():",
            "           pass",
            "       def mir():",
            "           pass",
        )
        FunctionTransformer().visit(source)

        foo = source.body[0]
        bar = foo.body[0]
        gib = bar.body[0]
        mir = bar.body[1]

        assert len(foo.defined_functions) == 1
        assert len(bar.defined_functions) == 2
        assert len(gib.defined_functions) == 0
        assert len(mir.defined_functions) == 0

    # def test_nested_functions(self):


class TestCalledWithTransformer:
    def test_var_called_with_later_function(self):
        source = parse(
            "x = 3",
            "bar(x)",
            "bar(foo(x))",
        )
        CalledWithTransformer().visit(source)

        x = source.body[0].targets[0]

        assert len(x.called_with) == 2
