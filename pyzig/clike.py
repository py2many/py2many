import ast
from keyword import kwlist, softkwlist

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import ZIG_CONTAINER_TYPE_MAP, ZIG_TYPE_MAP, ZIG_WIDTH_RANK

# allowed as names in Python but treated as keywords in Zig
zig_keywords = frozenset(
    kwlist
    + softkwlist
    # https://github.com/ziglang/zig-spec/blob/master/grammar/grammar.peg
    + [
        "addrspace",
        "align",
        "allowzero",
        "and",
        "anyframe",
        "anytype",
        "asm",
        "async",
        "await",
        "break",
        "callconv",
        "catch",
        "comptime",
        "const",
        "continue",
        "defer",
        "else",
        "enum",
        "errdefer",
        "error",
        "export",
        "extern",
        "fn",
        "for",
        "if",
        "inline",
        "noalias",
        "nosuspend",
        "noinline",
        "opaque",
        "or",
        "orelse",
        "packed",
        "pub",
        "resume",
        "return",
        "linksection",
        "struct",
        "suspend",
        "switch",
        "test",
        "threadlocal",
        "try",
        "union",
        "unreachable",
        "usingnamespace",
        "var",
        "volatile",
        "while",
    ]
) - frozenset(["_"])

zig_symbols = {
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
    ast.And: " and ",
    ast.Or: " or ",
    ast.In: "in",
}


def zig_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return zig_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = ZIG_TYPE_MAP
        CommonCLikeTranspiler._container_type_map = ZIG_CONTAINER_TYPE_MAP
        self._statement_separator = ";"

    def visit(self, node) -> str:
        if type(node) in zig_symbols:
            return zig_symbol(node)
        else:
            return super().visit(node)

    def visit_Ellipsis(self, node) -> str:
        return "pass"

    def visit_BinOp(self, node) -> str:

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node.right)

        left_rank = ZIG_WIDTH_RANK.get(left_type, -1)
        right_rank = ZIG_WIDTH_RANK.get(right_type, -1)

        left_is_float = left_type in ("f32", "f64")
        right_is_float = right_type in ("f32", "f64")

        if left_rank > right_rank and right_rank >= 0:
            if left_is_float and not right_is_float:
                right = f"@as({left_type}, @floatFromInt({right}))"
            elif not left_is_float and right_is_float:
                right = f"@as({left_type}, @intFromFloat({right}))"
            else:
                right = f"@as({left_type}, @intCast({right}))"
        elif right_rank > left_rank and left_rank >= 0:
            if right_is_float and not left_is_float:
                left = f"@as({right_type}, @floatFromInt({left}))"
            elif not right_is_float and left_is_float:
                left = f"@as({right_type}, @intFromFloat({left}))"
            else:
                left = f"@as({right_type}, @intCast({left}))"
        elif left_rank < 0 and right_is_float:
            # Left type unknown, right is float: cast left to float for the op
            left = f"@as({right_type}, @floatFromInt({left}))"
        elif right_rank < 0 and left_is_float:
            # Right type unknown, left is float: cast right to float for the op
            right = f"@as({left_type}, @floatFromInt({right}))"

        if isinstance(node.op, ast.Pow):
            wider_type = left_type if left_rank >= right_rank else right_type
            return f"std.math.pow({wider_type}, {left}, {right})"

        return f"({left} {op} {right})"

    def visit_Name(self, node) -> str:
        if node.id in zig_keywords:
            return node.id + "_"
        # Single underscore is the zig discard pattern
        if node.id == "_":
            return "_"
        # _-prefixed (but not __-prefixed) names follow Python's "unused"
        # convention; map them to zig's discard to avoid unused-variable errors.
        # __-prefixed names (like __tmp1 from rewriters) are kept as-is.
        if node.id.startswith("_") and not node.id.startswith("__"):
            return "_"
        return super().visit_Name(node)

    def _is_str(self, node) -> bool:
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return True
        return self._typename_from_annotation(node) in ("str", "string")

    def _is_list(self, node) -> bool:
        """Check if node has a List annotation (maps to zig slices)."""
        ann = getattr(node, "annotation", None)
        if ann is None:
            # Check the scope for the variable definition
            if isinstance(node, ast.Name):
                scopes = getattr(node, "scopes", None)
                if scopes:
                    defn = scopes.find(get_id(node))
                    ann = getattr(defn, "annotation", None)
        if ann is not None:
            if isinstance(ann, ast.Subscript):
                return get_id(ann.value) == "List"
        return False

    def _list_element_type(self, node):
        """Get the element type of a List annotation."""
        ann = getattr(node, "annotation", None)
        if ann is None and isinstance(node, ast.Name):
            scopes = getattr(node, "scopes", None)
            if scopes:
                defn = scopes.find(get_id(node))
                ann = getattr(defn, "annotation", None)
        if ann is not None and isinstance(ann, ast.Subscript):
            elt_node = ann.slice
            if isinstance(elt_node, ast.Index):
                elt_node = elt_node.value
            return self._typename_from_type_node(elt_node)
        return "i32"

    def visit_Compare(self, node) -> str:
        # Zig strings (``[]const u8``) compare with std.mem.eql, not ``==``.
        if isinstance(node.ops[0], (ast.Eq, ast.NotEq)) and (
            self._is_str(node.left) or self._is_str(node.comparators[0])
        ):
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            eql = f"std.mem.eql(u8, {left}, {right})"
            return f"!{eql}" if isinstance(node.ops[0], ast.NotEq) else eql

        # Zig slices compare with std.mem.eql, not ``==``.
        if isinstance(node.ops[0], (ast.Eq, ast.NotEq)) and (
            self._is_list(node.left) or self._is_list(node.comparators[0])
        ):
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            # Add & for Name nodes (arrays need address-of to coerce to slice)
            if isinstance(node.left, ast.Name):
                left = f"&{left}"
            if isinstance(node.comparators[0], ast.Name):
                right = f"&{right}"
            # Determine element type
            if self._is_list(node.left):
                elem_type = self._list_element_type(node.left)
            else:
                elem_type = self._list_element_type(node.comparators[0])
            eql = f"std.mem.eql({elem_type}, {left}, {right})"
            return f"!{eql}" if isinstance(node.ops[0], ast.NotEq) else eql

        return super().visit_Compare(node)

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        left_type = self._typename_from_annotation(node.left)
        if left_type == "string":
            self._usings.add("strutils")
        return f"{left} in {right}"

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "null"
        elif node.value is Ellipsis:
            return self.visit_Ellipsis(node)
        else:
            return node.value
