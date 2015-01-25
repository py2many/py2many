import ast
from scope import add_scope_context
from context import add_variable_context
from analysis import (FunctionTransformer, CalledWithTransformer,
                      ImportTransformer, AttributeCallTransformer)


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

    def test_functions_from_modules(self):
        source = parse("from foo import bar, baz")
        FunctionTransformer().visit(source)

        module = source

        assert len(module.defined_functions) == 2


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


class TestAttributeCallTransformer:
    def test_call_to_attribute_registered(self):
        source = parse(
            "x = foo()",
            "x.bar()",
        )
        AttributeCallTransformer().visit(source)

        x = source.body[0].targets[0]

        assert len(x.calls) == 1


class TestImportTransformer:
    def test_function_knows_from_where_it_is_imported(self):
        source = parse(
            "from foo import bar",
            "bar(x)",
        )
        ImportTransformer().visit(source)

        module = source
        bar_import = source.body[0].names[0]

        assert len(module.imports) == 1
        assert isinstance(bar_import.imported_from, ast.ImportFrom)
