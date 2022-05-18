import ast
from typing import Any

from py2many.ast_helpers import get_id
from py2many.tracer import find_node_by_name_and_type


def find_ordered_collections(node, extension=False):
    visitor = JuliaOrderedCollectionTransformer()
    visitor.visit(node)

class JuliaOrderedCollectionTransformer(ast.NodeTransformer):

    SPECIAL_FUNC_CALLS = set([
        "items",
        "keys",
        "values"
    ])

    def __init__(self) -> None:
        super().__init__()

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        if ann := getattr(node.value, "annotation", None):
            ann_id = ""
            if isinstance(ann, ast.Subscript):
                ann_id = get_id(ann.value)
            elif id := get_id(ann):
                ann_id = id
            if ann_id == "Dict" or ann_id == "Set":
                for t in node.targets:
                    t_id = get_id(t)
                    for spec_call_name in self.SPECIAL_FUNC_CALLS:
                        call_id = f"{t_id}.{spec_call_name}"
                        call_node = find_node_by_name_and_type(call_id, ast.Call, node.scopes)[0]
                        if call_node:
                            node.value.use_ordered_collection = True
                            break
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        self.generic_visit(node)
        ann_id = ""
        if isinstance(node.annotation, ast.Subscript):
            ann_id = get_id(node.annotation.value)
        elif id := get_id(node.annotation):
            ann_id = id
        if ann_id == "Dict" or ann_id == "Set":
            t_id = get_id(node.target)
            for spec_call_name in self.SPECIAL_FUNC_CALLS:
                call_id = f"{t_id}.{spec_call_name}"
                call_node = find_node_by_name_and_type(call_id, ast.Call, node.scopes)[0]
                if call_node:
                    node.value.use_ordered_collection = True
                    break
        return node


