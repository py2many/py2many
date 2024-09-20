import ast
from keyword import kwlist, softkwlist

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import MOJO_TYPE_MAP, MOJO_WIDTH_RANK

# allowed as names in Python but treated as keywords in Mojo
mojo_keywords = (
    frozenset(kwlist)
    + frozenset(softkwlist)
    + frozenset(
        ["fn", "var", "alias", "struct", "raises", "owned", "borrowed", "inout", "ref"]
    )
)

mojo_symbols = {
    ast.Eq: "==",
    ast.Is: "==",
    ast.NotEq: "!=",
    ast.Pass: "pass",
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
    ast.BitXor: "xor",
    ast.BitOr: "or",
    ast.BitAnd: "and",
    ast.Not: "not ",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: " and ",
    ast.Or: " or ",
    ast.In: "in",
}


def mojo_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return mojo_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = MOJO_TYPE_MAP
        self._statement_separator = ""

    def visit(self, node) -> str:
        if type(node) in mojo_symbols:
            return mojo_symbol(node)
        else:
            return super().visit(node)

    def visit_Ellipsis(self, node) -> str:
        return "pass"

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Pow):
            left = self.visit(node.left)
            right = self.visit(node.right)
            return f"{left}**{right}"

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node.right)

        left_rank = MOJO_WIDTH_RANK.get(left_type, -1)
        right_rank = MOJO_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"

        return f"({left} {op} {right})"

    def visit_Name(self, node) -> str:
        if node.id in mojo_keywords:
            return node.id + "_"
        if node.id.startswith("_"):
            return "_"
        return super().visit_Name(node)

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        left_type = self._typename_from_annotation(node.left)
        if left_type == "string":
            self._usings.add("strutils")
        return f"{left} in {right}"

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "True"
        elif node.value is False:
            return "False"
        elif node.value is None:
            return "None"
        elif node.value is Ellipsis:
            return self.visit_Ellipsis(node)
        else:
            return node.value
