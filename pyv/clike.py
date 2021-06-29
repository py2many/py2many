import ast

from .inference import V_TYPE_MAP, V_WIDTH_RANK

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


# allowed as names in Python but treated as keywords in V
v_keywords = frozenset(
    [
        "struct",
        "type",
        "match",
        "impl",
        "const",
        "enum",
        "extern",
        "fn",
        "loop",
        "move",
        "mut",
        "pub",
        "ref",
        "trait",
        "where",
        "use",
        "unsafe",
    ]
)

v_symbols = {
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
    ast.And: " && ",
    ast.Or: " || ",
    ast.In: "in",
}


def v_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return v_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = V_TYPE_MAP
        self._statement_separator = ""

    def visit(self, node):
        if type(node) in v_symbols:
            return v_symbol(node)
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

        left_rank = V_WIDTH_RANK.get(left_type, -1)
        right_rank = V_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"

        return f"({left} {op} {right})"

    def visit_Name(self, node):
        if node.id in v_keywords:
            return node.id + "_"
        if node.id.startswith("_"):
            return "_"
        return super().visit_Name(node)

    def visit_In(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"
