import ast

from py2many.pyrs.rust_ast import (
    RustAssignment,
    RustAugAssignment,
    RustAwait,
    RustCall,
    RustExprStatement,
    RustForLoop,
    RustFunction,
    RustIf,
    RustLet,
    RustLoop,
    RustMacroCall,
    RustNode,
    RustRawItem,
    RustRenderer,
    RustReturn,
    RustSourceFile,
    RustWhileLoop,
    RustYield,
)
from py2many.pyrs.transpiler import RustTranspiler


def test_rust_source_file_renders_in_a_separate_pass():
    rust_ast = RustSourceFile.from_items(
        [
            RustRawItem.from_source("pub const ANSWER: i32 = 42;"),
            RustRawItem.from_source("pub fn answer() -> i32 {\nreturn ANSWER;\n}\n"),
        ]
    )

    rendered = RustRenderer().render(rust_ast)

    assert (
        rendered
        == "pub const ANSWER: i32 = 42;\npub fn answer() -> i32 {\nreturn ANSWER;\n}\n"
    )


def test_tree_sitter_node_keeps_parse_tree_when_dependency_is_available():
    item = RustRawItem.from_source('pub fn main() {\nprintln!("OK");\n}\n')

    assert item.node.kind == "source_file"
    assert item.render().startswith("pub fn main()")


def test_simple_rust_ast_nodes_render_source():
    assert RustCall("fib", ["n - 1"]).render() == "fib(n - 1)"
    assert RustReturn("answer").render() == "return answer;"
    assert RustAssignment("answer", "42").render() == "answer = 42;"
    assert RustAugAssignment("answer", "+", "1").render() == "answer += 1;"
    assert RustLet("answer", "42", typename="i32").render() == "let answer: i32 = 42;"
    assert RustExprStatement("answer").render() == "answer;"
    assert RustFunction("pub fn answer() -> i32", [RustReturn("42")]).render() == (
        "pub fn answer() -> i32 {\nreturn 42;\n }\n"
    )
    assert RustForLoop("x", "xs", [RustExprStatement("x")]).render() == (
        "for x in xs {\nx;\n}"
    )
    assert RustWhileLoop("ready", [RustExprStatement("tick()")]).render() == (
        "while ready {\ntick();\n}"
    )
    assert RustLoop([RustExprStatement("tick()")]).render() == "loop {\ntick();\n}\n"
    assert RustIf("ready", [RustExprStatement("tick()")]).render() == (
        "if ready {\ntick();\n}"
    )
    assert RustMacroCall("assert", ["ready"]).render() == "assert!(ready);"
    assert RustAwait("future").render() == "future.await"
    assert RustYield("value").render() == "yield value;"


def test_rust_transpiler_visitors_return_tree_sitter_nodes():
    tree = ast.parse("def f() -> int:\n    return 42\n")
    function = tree.body[0]
    return_node = function.body[0]
    return_node.scopes = []
    transpiler = RustTranspiler(no_prologue=True)

    rendered_return = transpiler.visit(return_node)
    direct_return = transpiler.visit_Return(return_node)

    assert rendered_return.render() == "return 42;"
    assert rendered_return.kind == "source_file"
    assert isinstance(direct_return, RustNode)
    assert direct_return.render() == "return 42;"
