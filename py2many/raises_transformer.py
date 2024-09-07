import ast


def detect_raises(node):
    return RaisesTransformer().visit(node)


class RaisesTransformer(ast.NodeTransformer):
    """
    Annotates function def ast nodes with information about exceptions
    """

    def _mark_parent_raises(self, node):
        fndef = None
        for scope in node.scopes:
            if isinstance(scope, ast.FunctionDef):
                fndef = scope
                break
        if fndef is not None:
            fndef.raises = True

    def visit_Assert(self, node):
        self._mark_parent_raises(node)
        self.generic_visit(node)
        return node

    def visit_Call(self, node) -> str:
        fname = self.visit(node.func)
        fndef = node.scopes.find(fname)
        if fndef is not None and hasattr(fndef, "raises"):
            self._mark_parent_raises(node)
        self.generic_visit(node)
        return node
