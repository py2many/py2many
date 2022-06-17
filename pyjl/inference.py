import ast


def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)


class InferJuliaTypesTransformer(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_BinOp(self, node):
        self.generic_visit(node)

        # Detect nesting in binary operations
        if isinstance(node.left, ast.BinOp):
            node.left.isnested = True
        if isinstance(node.right, ast.BinOp):
            node.right.isnested = True
        return node
