import ast


class AstNotImplementedError(NotImplementedError):
    def __init__(self, msg: str, node: ast.AST):
        self.lineno = node.lineno
        self.col_offset = node.col_offset
        super().__init__(msg)
