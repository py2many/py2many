import ast

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import RUST_WIDTH_RANK, RUST_TYPE_MAP, is_rust_reference


# allowed as names in Python but treated as keywords in Rust
rust_keywords = frozenset(
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


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = RUST_TYPE_MAP

    def visit_Name(self, node):
        if node.id in rust_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            return "pow({0}, {1})".format(self.visit(node.left), self.visit(node.right))

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node.right)

        left_rank = RUST_WIDTH_RANK.get(left_type, -1)
        right_rank = RUST_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{right} as {left_type}"
        elif right_rank > left_rank:
            left = f"{left} as {right_type}"

        # Multiplication and division binds tighter (has higher precedence) than addition and subtraction.
        # To visually communicate this we omit spaces when multiplying and dividing.
        if isinstance(node.op, (ast.Mult, ast.Div)):
            return f"({left}{op}{right})"
        else:
            return f"({left} {op} {right})"

    def visit_Compare(self, node):
        if isinstance(node.ops[0], ast.In):
            return self.visit_In(node)

        node_right = node.comparators[0]
        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node_right)

        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node_right)

        if not is_rust_reference(node.left) and is_rust_reference(node_right):
            right = f"*{right}"

        if is_rust_reference(node.left) and not is_rust_reference(node_right):
            left = f"*{left}"

        left_rank = RUST_WIDTH_RANK.get(left_type, -1)
        right_rank = RUST_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{right} as {left_type}"
        elif right_rank > left_rank:
            left = f"{left} as {right_type}"

        return f"{left} {op} {right}"

    def visit_In(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return "{0}.any({1})".format(right, left)
