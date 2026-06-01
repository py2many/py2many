import ast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node


class LeanImplicitConstructor(ast.NodeTransformer):
    """Give plain classes an explicit empty __init__ so the backend can emit a
    structure constructor, mirroring the other backends."""

    def visit_ClassDef(self, node):
        needs_init = "dataclass" not in [get_id(n) for n in node.decorator_list]
        for b in node.body:
            if isinstance(b, ast.FunctionDef) and b.name == "__init__":
                needs_init = False

        if not needs_init:
            return node

        new_node = create_ast_node("def __init__(self): pass")
        ast.fix_missing_locations(new_node)
        node.body.insert(0, new_node)
        return node
