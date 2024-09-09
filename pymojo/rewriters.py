import ast

from py2many.ast_helpers import create_ast_node


class MojoImplicitConstructor(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node):
        has_implicit_init = True
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                if b.name == "__init__":
                    has_implicit_init = False

        if not has_implicit_init:
            return node

        new_node = create_ast_node("def __init__(self): pass")
        ast.fix_missing_locations(new_node)
        node.body.insert(0, new_node)
        return node
