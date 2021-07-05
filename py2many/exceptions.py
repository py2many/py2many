import ast


class AstErrorBase:
    def __init__(self, msg: str, node: ast.AST):
        self.lineno = node.lineno
        self.col_offset = node.col_offset
        super().__init__(msg)  # noqa: other mechanisms of subclassing Exception


class AstNotImplementedError(AstErrorBase, NotImplementedError):
    """Node is not supported by the transpiler"""


class AstUnrecognisedBinOp(AstNotImplementedError):
    """BinOp using unrecognised combination"""

    def __init__(self, left_id: str, right_id: str, node: ast.AST):
        self.lineno = node.lineno
        self.col_offset = node.col_offset
        super().__init__(f"{left_id} {type(node.op)} {right_id}", node)


class AstIncompatibleAssign(AstErrorBase, TypeError):
    """Assignment target has type annotation that is incompatible with expression"""


class AstEmptyNodeFound(TypeError):
    def __init__(self):
        super().__init__("node can not be None")
