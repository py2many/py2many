import ast
from py14.clike import cpp_symbol


def test_cpp_symbol():
    source = ast.parse("x == y")
    equals_symbol = source.body[0].value.ops[0]
    assert cpp_symbol(equals_symbol) == "=="
