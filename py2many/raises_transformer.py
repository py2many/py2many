import ast


def detect_raises(node):
    return RaisesTransformer().visit(node)


class RaisesTransformer(ast.NodeTransformer):
    """
    Annotates function def ast nodes with information about exceptions
    """
    def visit_Assert(self, node):
        fndef = None
        for scope in node.scopes:
            if isinstance(scope, ast.FunctionDef):
                fndef = scope
                break
        if fndef is not None:
            fndef.raises = True
        self.generic_visit(node)
        return node
