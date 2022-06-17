import ast


class JuliaMainRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_If(self, node):
        is_main = (
            isinstance(node.test, ast.Compare)
            and isinstance(node.test.left, ast.Name)
            and node.test.left.id == "__name__"
            and isinstance(node.test.ops[0], ast.Eq)
            and isinstance(node.test.comparators[0], ast.Constant)
            and node.test.comparators[0].value == "__main__"
        )
        if is_main:
            node.python_main = is_main
            node.test.left = ast.Call(
                func=ast.Name(id="abspath"),
                args=[ast.Name(id="PROGRAM_FILE")],
                keywords=[],
                scopes=node.test.left.scopes,
                lineno=node.test.left.lineno,
                col_offset=node.test.left.col_offset,
            )
            node.test.comparators[0] = ast.Name(id="@__FILE__")
        return node
