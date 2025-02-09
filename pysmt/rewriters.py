import ast

from py2many.analysis import get_id


class AnnotatePreConditions(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_If(self, node):
        check = get_id(node.test)
        if check == "smt_pre":
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                fndef.is_smt_pre = True
        return node
