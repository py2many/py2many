import ast
from keyword import kwlist, softkwlist

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import LEAN_CONTAINER_TYPE_MAP, LEAN_TYPE_MAP

# allowed as names in Python but reserved (keywords/notation) in Lean 4
lean_keywords = frozenset(
    kwlist
    + softkwlist
    + [
        "by",
        "calc",
        "deriving",
        "do",
        "else",
        "end",
        "example",
        "extends",
        "fun",
        "have",
        "if",
        "inductive",
        "instance",
        "let",
        "match",
        "namespace",
        "open",
        "partial",
        "section",
        "set_option",
        "structure",
        "theorem",
        "then",
        "universe",
        "variable",
        "where",
        "with",
    ]
) - frozenset(["_"])

lean_symbols = {
    ast.Eq: "==",
    ast.Is: "==",
    ast.NotEq: "!=",
    ast.Pass: "pure ()",
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
    ast.LShift: "<<<",
    ast.RShift: ">>>",
    ast.BitXor: "^^^",
    ast.BitOr: "|||",
    ast.BitAnd: "&&&",
    ast.Not: "!",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: " && ",
    ast.Or: " || ",
    ast.In: "in",
}


def lean_symbol(node):
    """Find the equivalent Lean symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return lean_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = LEAN_TYPE_MAP
        CommonCLikeTranspiler._container_type_map = LEAN_CONTAINER_TYPE_MAP
        # Lean statements inside a `do` block are newline-separated, with no
        # trailing terminator.
        self._statement_separator = ""

    def visit(self, node) -> str:
        if type(node) in lean_symbols:
            return lean_symbol(node)
        else:
            return super().visit(node)

    def visit_Ellipsis(self, node) -> str:
        return "pure ()"

    def visit_BinOp(self, node) -> str:
        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        if isinstance(node.op, ast.Pow):
            return f"({left} ^ {right})"

        return f"({left} {op} {right})"

    def visit_Name(self, node) -> str:
        if node.id in lean_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"({left} ∈ {right})"

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "none"
        elif node.value is Ellipsis:
            return self.visit_Ellipsis(node)
        else:
            return node.value
