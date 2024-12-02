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

dlang_type_map = {
    bool: "bool",
    int: "int",
    float: "double",
    bytes: "Uint8List",
    str: "string",
    c_int8: "byte",
    c_int16: "short",
    c_int32: "int",
    c_int64: "long",
    c_uint8: "ubyte",
    c_uint16: "ushort",
    c_uint32: "uint",
    c_uint64: "ulong",
}

DLANG_CONTAINER_TYPE_MAP = {
    "List": "[]",
    "Dict": "Map",
    "Set": "auto",  # RedBlackTree
    "Optional": "Nothing",
}

# allowed as names in Python but treated as keywords in dlang
dlang_keywords = frozenset(
    [
        "assert",
        "break",
        "case",
        "catch",
        "class",
        "const",
        "continue",
        "default",
        "do",
        "else",
        "enum",
        "extends",
        "false",
        "final",
        "finally",
        "for",
        "if",
        "in",
        "is",
        "new",
        "null",
        "rethrow",
        "return",
        "super",
        "switch",
        "this",
        "throw",
        "true",
        "try",
        "var",
        "void",
        "while",
        "with",
    ]
)


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = dlang_type_map
        CommonCLikeTranspiler._container_type_map = DLANG_CONTAINER_TYPE_MAP

    def visit_Name(self, node) -> str:
        if node.id in dlang_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def is_complex(self, node):
        return isinstance(node, ast.Constant) and isinstance(node.value, complex)

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Pow):
            return f"pow({self.visit(node.left)}, {self.visit(node.right)})"

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        # Multiplication and division binds tighter (has higher precedence) than addition and subtraction.
        # To visually communicate this we omit spaces when multiplying and dividing.
        if isinstance(node.op, (ast.Mult, ast.Div)):
            if getattr(node, "use_integer_div", False):
                # NOTE: no such operator in Dlang: Use integer division operator
                op = "/"
            return f"({left}{op}{right})"
        else:
            return f"({left} {op} {right})"

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{right}.any({left})"
