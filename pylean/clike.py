import ast
from keyword import kwlist, softkwlist

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import LEAN_CONTAINER_TYPE_MAP, LEAN_TYPE_MAP, LEAN_WIDTH_RANK

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

    @staticmethod
    def _is_bool_operand(node) -> bool:
        """Return True when a BinOp operand is known to be Bool."""
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return True
        if isinstance(node, ast.Name):
            ann = getattr(node, "annotation", None)
            if ann and get_id(ann) == "bool":
                return True
        return False

    # Map Python annotation id strings (e.g. "c_int8") to Lean type names
    _PYNAME_TO_LEAN = {
        "c_int8": "Int8",
        "c_int16": "Int16",
        "c_int32": "Int32",
        "c_int64": "Int64",
        "c_uint8": "UInt8",
        "c_uint16": "UInt16",
        "c_uint32": "UInt32",
        "c_uint64": "UInt64",
        "int": "Nat",
        "float": "Float",
        "bool": "Bool",
    }

    @classmethod
    def _get_node_type_id(cls, node) -> str:
        """Return the Lean type name for an AST node, or empty string."""
        # First check lean_annotation (set by InferLeanTypesTransformer)
        lean_ann = getattr(node, "lean_annotation", None)
        if lean_ann and lean_ann in LEAN_WIDTH_RANK:
            return lean_ann
        ann = getattr(node, "annotation", None)
        if ann:
            aid = get_id(ann)
            if aid:
                # Try direct Lean name
                if aid in LEAN_WIDTH_RANK:
                    return aid
                # Try mapping from Python name
                mapped = cls._PYNAME_TO_LEAN.get(aid, "")
                if mapped and mapped in LEAN_WIDTH_RANK:
                    return mapped
        return ""

    _SIGNED_FW = {"Int8", "Int16", "Int32", "Int64"}
    _UNSIGNED_FW = {"UInt8", "UInt16", "UInt32", "UInt64"}

    @classmethod
    def _lean_cast(cls, expr: str, from_type: str, to_type: str) -> str:
        """Wrap *expr* in a cast from *from_type* to *to_type*.

        Lean fixed-width types don't implicitly widen, so we generate
        an explicit conversion chain via Int or Nat as intermediate.
        """
        if from_type == to_type or not from_type or not to_type:
            return expr

        from_signed = from_type in cls._SIGNED_FW
        from_unsigned = from_type in cls._UNSIGNED_FW

        # Float target
        if to_type == "Float":
            if from_signed:
                return f"(Float.ofInt {expr}.toInt)"
            if from_unsigned:
                return f"(Float.ofNat {expr}.toNat)"
            return f"(Float.ofNat {expr})"

        # Fixed-width target: go through Int (for signed src) or Nat (for unsigned src)
        if to_type in cls._SIGNED_FW or to_type in cls._UNSIGNED_FW:
            if from_signed:
                return f"({to_type}.ofInt {expr}.toInt)"
            if from_unsigned:
                return f"({to_type}.ofNat {expr}.toNat)"
            # from Nat/Int
            if from_type == "Nat":
                return f"({to_type}.ofNat {expr})"
            return f"({to_type}.ofInt {expr})"

        return f"({expr} : {to_type})"

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

        # Bool bitwise ops: Python's &, |, ^ on bools should map to &&, ||, xor
        if isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            if self._is_bool_operand(node.left) or self._is_bool_operand(node.right):
                if isinstance(node.op, ast.BitAnd):
                    return f"({left} && {right})"
                elif isinstance(node.op, ast.BitOr):
                    return f"({left} || {right})"
                else:  # BitXor
                    return f"(xor {left} {right})"

        # Fixed-width integer widening casts.
        # When the inferred result type is wider than the operand types,
        # insert explicit casts so that both operands match the result type.
        cast_applied = False
        result_type = getattr(node, "lean_annotation", None)
        if result_type and result_type in LEAN_WIDTH_RANK:
            left_type = self._get_node_type_id(node.left)
            right_type = self._get_node_type_id(node.right)
            if left_type and left_type != result_type:
                left = self._lean_cast(left, left_type, result_type)
                cast_applied = True
            if right_type and right_type != result_type:
                right = self._lean_cast(right, right_type, result_type)
                cast_applied = True

        # When mixing Float and non-Float operands, ensure both are Float
        # so Lean's type checker is happy.  Skip if widening cast already handled.
        if not cast_applied:
            left_is_float = (
                isinstance(node.left, ast.Constant)
                and isinstance(node.left.value, float)
            ) or self._get_node_type_id(node.left) == "Float"
            right_is_float = (
                isinstance(node.right, ast.Constant)
                and isinstance(node.right.value, float)
            ) or self._get_node_type_id(node.right) == "Float"
            if left_is_float and not right_is_float:
                right = f"(Float.ofNat {right})"
            elif right_is_float and not left_is_float:
                left = f"(Float.ofNat {left})"

        return f"({left} {op} {right})"

    def visit_BoolOp(self, node) -> str:
        # Parenthesise so precedence is preserved when a boolean expression is
        # an operand of a tighter operator -- Lean binds ``==`` tighter than
        # ``&&``, so ``(a and b) == c`` must emit ``(a && b) == c`` rather than
        # ``a && b == c`` (which parses as ``a && (b == c)``).
        op = self.visit(node.op)
        return "(" + op.join([self.visit(v) for v in node.values]) + ")"

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

        # Handle comparisons with None: ``x != None`` → ``true``,
        # ``x == None`` → ``false`` (for non-Option types).
        for op, comp in zip(node.ops, node.comparators):
            if isinstance(comp, ast.Constant) and comp.value is None:
                if isinstance(op, (ast.NotEq, ast.IsNot)):
                    return "true"
                if isinstance(op, (ast.Eq, ast.Is)):
                    return "false"
            if isinstance(node.left, ast.Constant) and node.left.value is None:
                if isinstance(op, (ast.NotEq, ast.IsNot)):
                    return "true"
                if isinstance(op, (ast.Eq, ast.Is)):
                    return "false"

        # Handle Float/Nat comparison by converting Nat side to Float
        result = super().visit_Compare(node)
        left_type = self._get_node_type_id(node.left)
        if left_type == "Float" and node.comparators:
            comp = node.comparators[0]
            if isinstance(comp, ast.Constant) and isinstance(comp.value, (int, float)):
                if isinstance(comp.value, int):
                    left = self.visit(node.left)
                    op = self.visit(node.ops[0])
                    right = f"(Float.ofNat {self.visit(comp)})"
                    return f"({left} {op} {right})"
        return result

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
