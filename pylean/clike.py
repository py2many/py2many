import ast
from keyword import kwlist, softkwlist

from py2many.analysis import get_id
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
        "show",
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

    @classmethod
    def _combine_value_index(cls, value_type, index_type) -> str:
        """Lean uses juxtaposition for type application: ``List Int``."""
        if isinstance(index_type, list):
            index_type = " ".join(index_type)
        return f"{value_type} {index_type}"

    def visit(self, node) -> str:
        if type(node) in lean_symbols:
            return lean_symbol(node)
        else:
            return super().visit(node)

    def visit_Ellipsis(self, node) -> str:
        return "pure ()"

    def _is_bool(self, node) -> bool:
        """Best-effort check that an expression is a Lean ``Bool``."""
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return True
        ann = getattr(node, "annotation", None)
        if ann is None and isinstance(node, ast.Name) and hasattr(node, "scopes"):
            var = node.scopes.find(get_id(node))
            ann = getattr(var, "annotation", None)
        return get_id(ann) in ("bool", "Bool")

    def visit_BinOp(self, node) -> str:
        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        if isinstance(node.op, ast.Pow):
            return f"({left} ^ {right})"

        # Python's &, |, ^ on bool are logical; Lean's integer bit operators
        # (&&&, |||, ^^^) don't apply to Bool, so emit the boolean operators.
        if isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)) and (
            self._is_bool(node.left) and self._is_bool(node.right)
        ):
            if isinstance(node.op, ast.BitAnd):
                return f"({left} && {right})"
            if isinstance(node.op, ast.BitOr):
                return f"({left} || {right})"
            return f"(xor {left} {right})"

        # When dividing by a float literal (or vice versa), ensure the other
        # operand is also a Float so Lean's type checker is happy.
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            left_is_float = isinstance(node.left, ast.Constant) and isinstance(
                node.left.value, float
            )
            right_is_float = isinstance(node.right, ast.Constant) and isinstance(
                node.right.value, float
            )
            if right_is_float and not left_is_float:
                left = f"(Float.ofNat {left})"
            elif left_is_float and not right_is_float:
                right = f"(Float.ofNat {right})"

        return f"({left} {op} {right})"

    @staticmethod
    def _rename_keyword(name: str) -> str:
        """Append ``_`` to names that clash with Lean keywords."""
        if name in lean_keywords:
            return name + "_"
        return name

    def visit_Name(self, node) -> str:
        return self._rename_keyword(super().visit_Name(node))

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"({right}).contains {left}"

    def visit_Compare(self, node) -> str:
        if isinstance(node.ops[0], ast.In):
            return self.visit_In(node)
        if isinstance(node.ops[0], ast.NotIn):
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            return f"!({right}).contains {left}"
        return super().visit_Compare(node)

    def visit_Bytes(self, node) -> str:
        # Python byte literals (b"...") map to a Lean ByteArray.
        data = self._get_bytes(node)
        elts = ", ".join(str(b) for b in data)
        return f"(⟨#[{elts}]⟩ : ByteArray)"

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
