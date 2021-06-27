import ast


class AstErrorBase:
    def __init__(self, msg: str, node: ast.AST):
        self.lineno = node.lineno
        self.col_offset = node.col_offset
        super().__init__(msg)


class AstNotImplementedError(AstErrorBase, NotImplementedError):
    """Node is not supported by the transpiler"""


class AstIncompatibleAssign(AstErrorBase, TypeError):
    """Assignment target has type annotation that is incompatible with expression"""
