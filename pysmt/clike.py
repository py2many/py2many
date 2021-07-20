import ast

from .inference import SMT_TYPE_MAP, SMT_WIDTH_RANK

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


# allowed as names in Python but treated as keywords in Smt
smt_keywords = frozenset([])

smt_symbols = {
    ast.Eq: "=",
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
    ast.BitXor: "xor",
    ast.BitOr: "or",
    ast.BitAnd: "and",
    ast.Not: "not",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: "and",
    ast.Or: "or",
    ast.In: "in",
}


def smt_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return smt_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = SMT_TYPE_MAP
        self._statement_separator = ""

    def visit(self, node):
        if type(node) in smt_symbols:
            return smt_symbol(node)
        else:
            return super().visit(node)

    def visit_Ellipsis(self, node):
        return "discard"

    def visit_UnaryOp(self, node):
        return "({0} {1})".format(self.visit(node.op), self.visit(node.operand))

    def visit_BoolOp(self, node):
        op = self.visit(node.op)
        values = " ".join([self.visit(v) for v in node.values])
        return f"({op} {values})"

    def visit_Compare(self, node):
        if isinstance(node.ops[0], ast.In):
            return self.visit_In(node)

        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node.comparators[0])

        return f"({op} {left} {right})"

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

        left_rank = SMT_WIDTH_RANK.get(left_type, -1)
        right_rank = SMT_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"

        return f"({op} {left} {right})"

    def visit_Name(self, node):
        if node.id in smt_keywords:
            return node.id + "_"
        return node.id.replace("_", "-")

    def visit_In(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        left_type = self._typename_from_annotation(node.left)
        if left_type == "string":
            self._usings.add("strutils")
        return f"{left} in {right}"
