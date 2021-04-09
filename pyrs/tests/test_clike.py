import ast
from py2many.clike import c_symbol


def test_c_symbol():
    source = ast.parse("x == y")
    equals_symbol = source.body[0].value.ops[0]
    assert c_symbol(equals_symbol) == "=="
