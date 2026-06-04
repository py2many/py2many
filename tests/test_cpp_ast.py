import ast

from py2many.analysis import add_imports
from py2many.context import add_list_calls, add_variable_context
from py2many.pycpp.cpp_ast import (
    CppAssignment,
    CppAugAssignment,
    CppCall,
    CppDeclaration,
    CppExprStatement,
    CppFunction,
    CppNode,
    CppRawItem,
    CppRenderer,
    CppReturn,
    CppSourceFile,
)
from py2many.pycpp.transpiler import CppTranspiler
from py2many.scope import add_scope_context


def _prepare_tree(source: str) -> ast.Module:
    tree = ast.parse(source)
    add_variable_context(tree, (tree,))
    add_scope_context(tree)
    add_list_calls(tree)
    add_imports(tree)
    return tree


def test_cpp_source_file_renders_in_a_separate_pass():
    cpp_ast = CppSourceFile.from_items(
        [
            CppRawItem.from_source("#include <cstdint>"),
            CppRawItem.from_source("int answer() {\nreturn 42;\n}\n"),
        ]
    )

    rendered = CppRenderer().render(cpp_ast)

    assert rendered == "#include <cstdint>\nint answer() {\nreturn 42;\n}\n"


def test_tree_sitter_node_keeps_cpp_parse_tree_when_dependency_is_available():
    item = CppRawItem.from_source("int main() {\nreturn 0;\n}\n")

    assert item.node.kind == "translation_unit"
    assert item.render().startswith("int main()")


def test_simple_cpp_ast_nodes_render_source():
    assert CppCall("fib", ["n - 1"]).render() == "fib(n - 1)"
    assert CppReturn("answer").render() == "return answer;"
    assert CppAssignment("answer", "42").render() == "answer = 42;"
    assert CppAugAssignment("answer", "+", "1").render() == "answer += 1;"
    assert CppDeclaration("int", "answer", "42").render() == "int answer = 42;"
    assert CppExprStatement("answer").render() == "answer;"
    assert CppFunction("int answer()", [CppReturn("42")]).render() == (
        "int answer() {\nreturn 42;\n}\n"
    )


def test_cpp_transpiler_simple_visitors_return_tree_sitter_nodes():
    tree = _prepare_tree(
        "def f(x: int) -> int:\n"
        "    y: int = inc(x)\n"
        "    y = inc(y)\n"
        "    y += 1\n"
        "    return y\n"
    )
    function = tree.body[0]
    declaration = function.body[0]
    assignment = function.body[1]
    aug_assignment = function.body[2]
    return_node = function.body[3]
    transpiler = CppTranspiler(no_prologue=True)

    rendered_call = transpiler.visit_Call(declaration.value)
    rendered_return = transpiler.visit_Return(return_node)
    rendered_declaration = transpiler.visit_AnnAssign(declaration)
    rendered_assignment = transpiler.visit_Assign(assignment)
    rendered_aug_assignment = transpiler.visit_AugAssign(aug_assignment)
    rendered_function = transpiler.visit_FunctionDef(function)

    assert isinstance(rendered_call, CppNode)
    assert rendered_call.render() == "inc(x)"
    assert rendered_return.render() == "return y;"
    assert rendered_declaration.render() == "int y = inc(x);"
    assert rendered_assignment.render() == "y = inc(y);"
    assert rendered_aug_assignment.render() == "y += 1;"
    assert rendered_function.render() == (
        "inline int f(int x) {\n"
        "int y = inc(x);\n"
        "y = inc(y);\n"
        "y += 1;\n"
        "return y;\n"
        "}\n"
    )
