import ast
from ctypes import (
    c_int8,
    c_int16,
    c_int32,
    c_int64,
    c_uint8,
    c_uint16,
    c_uint32,
    c_uint64,
)

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

julia_type_map = {
    bool: "Bool",
    int: "Int64",
    float: "Float64",
    bytes: "Array{UInt8}",
    str: "String",
    c_int8: "Int8",
    c_int16: "Int16",
    c_int32: "Int32",
    c_int64: "Int64",
    c_uint8: "UInt8",
    c_uint16: "UInt16",
    c_uint32: "UInt32",
    c_uint64: "UInt64",
}

JULIA_CONTAINER_TYPE_MAP = {
    "List": "Array",
    "Dict": "Dict",
    "Set": "Set",
    "Optional": "Nothing",
}

# allowed as names in Python but treated as keywords in Julia
julia_keywords = frozenset(
    [
        "abstract",
        "baremodule",
        "begin",
        "break",
        "catch",
        "const",
        "continue",
        "do",
        "else",
        "elseif",
        "end",
        "export",
        "false",
        "finally",
        "for",
        "function",
        "global",
        "if",
        "import",
        "let",
        "local",
        "macro",
        "module",
        "mutable",
        "primitive",
        "quote",
        "return",
        "struct",
        "true",
        "try",
        "type",
        "using",
        "while",
    ]
)

JL_SYMBOLS = {
    ast.BitXor: "⊻",
    ast.And: "&&",
    ast.Or: "||",
    ast.Is: "===",
    ast.IsNot: "!==",
}


def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return JL_SYMBOLS[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = julia_type_map

    def visit(self, node) -> str:
        if type(node) in JL_SYMBOLS:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node) -> str:
        if node.id in julia_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Mult):
            return f"{self.visit(node.left)}*{self.visit(node.right)}"
        if isinstance(node.op, ast.Pow):
            return f"{self.visit(node.left)}^{self.visit(node.right)}"

        bin_op = (
            f"{self.visit(node.left)} {self.visit(node.op)} {self.visit(node.right)}"
        )
        is_nested = getattr(node, "isnested", None)
        return bin_op if not is_nested else f"({bin_op})"

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"
