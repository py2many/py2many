import ast
from typing import Dict, Set

from .inference import V_TYPE_MAP, V_WIDTH_RANK

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


# allowed as names in Python but treated as keywords in V
v_keywords: Set[str] = frozenset(
    [
        "as",
        "asm",
        "assert",
        "atomic",
        "break",
        "const",
        "continue",
        "defer",
        "else",
        "enum",
        "false",
        "for",
        "fn",
        "__global",
        "go",
        "goto",
        "if",
        "import",
        "in",
        "interface",
        "is",
        "match",
        "module",
        "mut",
        "shared",
        "lock",
        "rlock",
        "none",
        "return",
        "select",
        "sizeof",
        "isreftype",
        "_likely_",
        "_unlikely_",
        "__offsetof",
        "struct",
        "true",
        "type",
        "typeof",
        "dump",
        "or",
        "union",
        "pub",
        "static",
        "unsafe",
    ]
)

v_symbols: Dict[type, str] = {
    ast.Eq: "==",
    ast.Is: "==",
    ast.NotEq: "!=",
    ast.Pass: "",
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
    ast.Not: "!",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: "&&",
    ast.Or: "||",
    ast.In: "in",
}


def v_symbol(node: ast.AST) -> str:
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return v_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = V_TYPE_MAP
        self._statement_separator: str = ""

    def visit(self, node: ast.AST) -> str:
        if type(node) in v_symbols:
            return v_symbol(node)
        else:
            return super().visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> str:
        if isinstance(node.op, ast.Pow):
            left: str = self.visit(node.left)
            right: str = self.visit(node.right)
            return f"{left}^{right}"

        left: str = self.visit(node.left)
        op: str = self.visit(node.op)
        right: str = self.visit(node.right)

        left_type: str = self._typename_from_annotation(node.left)
        right_type: str = self._typename_from_annotation(node.right)

        left_rank: int = V_WIDTH_RANK.get(left_type, -1)
        right_rank: int = V_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"
        if "bool" in (left_type, right_type):
            op = {"&": "&&", "|": "||", "^": "!="}.get(op, op)
        return f"({left} {op} {right})"

    def visit_Name(self, node: ast.Name) -> str:
        if node.id in v_keywords:
            return f"@{node.id}"
        return super().visit_Name(node)

    def visit_In(self, node: ast.Compare) -> str:
        left: str = self.visit(node.left)
        right: str = self.visit(node.comparators[0])
        return f"{left} in {right}"
