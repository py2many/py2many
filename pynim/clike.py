import ast

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


nim_type_map = {
    "int": "int",
    "float": "float",
    "bytes": "openArray[byte]",
    "str": "string",
    "bool": "bool",
    "c_int8": "int8",
    "c_int16": "int16",
    "c_int32": "int32",
    "c_int64": "int64",
    "c_uint8": "uint8",
    "c_uint16": "uint16",
    "c_uint32": "uint32",
    "c_uint64": "uint64",
}

NIM_WIDTH_RANK = {
    "int8": 0,
    "unt8": 1,
    "int16": 2,
    "unt16": 3,
    "int32": 4,
    "unt32": 5,
    "int64": 6,
    "unt64": 7,
    "float32": 8,
    "float64": 9,
    "float": 9,
}


# allowed as names in Python but treated as keywords in Nim
nim_keywords = frozenset(
    [
        "addr",
        "and",
        "as",
        "asm",
        "bind",
        "block",
        "break",
        "case",
        "cast",
        "concept",
        "const",
        "continue",
        "converter",
        "defer",
        "discard",
        "distinct",
        "div",
        "do",
        "elif",
        "else",
        "end",
        "enum",
        "except",
        "export",
        "finally",
        "for",
        "from",
        "func",
        "if",
        "import",
        "in",
        "include",
        "interface",
        "is",
        "isnot",
        "iterator",
        "let",
        "macro",
        "method",
        "mixin",
        "mod",
        "nil",
        "not",
        "notin",
        "object",
        "of",
        "or",
        "out",
        "proc",
        "ptr",
        "raise",
        "ref",
        "return",
        "shl",
        "shr",
        "static",
        "template",
        "try",
        "tuple",
        "type",
        "using",
        "var",
        "when",
        "while",
        "xor",
        "yield",
    ]
)

nim_symbols = {
    ast.Eq: "==",
    ast.Is: "==",
    ast.NotEq: "!=",
    ast.Pass: "discard",
    ast.Mult: "*",
    ast.Add: "+",
    ast.Sub: "-",
    ast.Div: "/",
    ast.FloorDiv: "/",
    ast.Mod: "%",
    ast.Lt: "<",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.LtE: "<=",
    ast.LShift: "<<",
    ast.RShift: ">>",
    ast.BitXor: "^",
    ast.BitOr: "|",
    ast.BitAnd: "&",
    ast.Not: "not ",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: " and ",
    ast.Or: " or ",
    ast.In: "in",
}


def nim_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return nim_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = nim_type_map

    def visit(self, node):
        if type(node) in nim_symbols:
            return nim_symbol(node)
        else:
            return super().visit(node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            left = self.visit(node.left)
            right = self.visit(node.right)
            return f"{left}^{right}"

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node.right)

        left_rank = NIM_WIDTH_RANK.get(left_type, -1)
        right_rank = NIM_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"

        return f"({left} {op} {right})"

    def visit_Name(self, node):
        if node.id in nim_keywords:
            return node.id + "_"
        if node.id.startswith("_"):
            return "_"
        return super().visit_Name(node)

    def visit_In(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"
