import ast
import ast as py_ast
from typing import Dict, Set

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import (
    V_CONTAINER_TYPE_MAP,
    V_TYPE_MAP,
    V_WIDTH_RANK,
    get_inferred_v_type,
)

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
    py_ast.Eq: "==",
    py_ast.Is: "==",
    py_ast.NotEq: "!=",
    py_ast.Pass: "",
    py_ast.Mult: "*",
    py_ast.Add: "+",
    py_ast.Sub: "-",
    py_ast.Div: "/",
    py_ast.FloorDiv: "/",
    py_ast.Mod: "%",
    py_ast.Lt: "<",
    py_ast.Gt: ">",
    py_ast.GtE: ">=",
    py_ast.LtE: "<=",
    py_ast.LShift: "<<",
    py_ast.RShift: ">>",
    py_ast.BitXor: "^",
    py_ast.BitOr: "|",
    py_ast.BitAnd: "&",
    py_ast.Not: "!",
    py_ast.IsNot: "!=",
    py_ast.USub: "-",
    py_ast.And: "&&",
    py_ast.Or: "||",
    py_ast.In: "in",
}


def v_symbol(node: py_ast.AST) -> str:
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return v_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = V_TYPE_MAP
        CommonCLikeTranspiler._container_type_map = V_CONTAINER_TYPE_MAP
        self._statement_separator: str = ""

    @classmethod
    def _typename_from_type_node(cls, node) -> str:
        if isinstance(node, py_ast.Constant) and node.value is Ellipsis:
            return "Any"
        return super()._typename_from_type_node(node)

    def visit(self, node: py_ast.AST) -> str:
        if type(node) in v_symbols:
            return v_symbol(node)
        else:
            return super().visit(node)

    def visit_BinOp(self, node: py_ast.BinOp) -> str:
        if isinstance(node.op, py_ast.Pow):
            left: str = self.visit(node.left)
            right: str = self.visit(node.right)
            return f"{left}^{right}"

        left: str = self.visit(node.left)
        op: str = self.visit(node.op)
        right: str = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        if not left_type or left_type == self._default_type:
            left_type = get_inferred_v_type(node.left)

        right_type = self._typename_from_annotation(node.right)
        if not right_type or right_type == self._default_type:
            right_type = get_inferred_v_type(node.right)

        left_rank: int = V_WIDTH_RANK.get(left_type, -1)
        right_rank: int = V_WIDTH_RANK.get(right_type, -1)

        if isinstance(node.op, py_ast.Mult):
            if left_type == "string" and right_type == "int":
                return f"({left}.repeat({right}))"
            if left_type and left_type.startswith("[]") and right_type == "int":
                return f"({left}.repeat({right}))"

        if left_rank > right_rank:
            right = (
                f"CAST_INT({right})" if left_type == "int" else f"{left_type}({right})"
            )
        elif right_rank > left_rank:
            left = (
                f"CAST_INT({left})" if right_type == "int" else f"{right_type}({left})"
            )
        if left_type and right_type and "bool" in (left_type, right_type):
            op = {"&": "&&", "|": "||", "^": "!="}.get(op, op)
        return f"({left} {op} {right})"

    def visit_Name(self, node: py_ast.Name) -> str:
        try:
            if node.id in v_keywords:
                return f"@{node.id}"
            return super().visit_Name(node)
        except Exception:
            import traceback

            traceback.print_exc()
            raise

    def visit_In(self, node: py_ast.Compare) -> str:
        left: str = self.visit(node.left)
        right: str = self.visit(node.comparators[0])
        return f"{left} in {right}"
