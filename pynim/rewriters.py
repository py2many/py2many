import ast
from py2many.ast_helpers import create_ast_block

class WithToBlockRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        return f"tmp{self._temp}"

    def visit_With(self, node):
        self.generic_visit(node)
        stmts = []
        for i in node.items:
            if i.optional_vars:
                target = i.optional_vars
            else:
                target = ast.Name(id=self._get_temp(), lineno=node.lineno)
            stmt = ast.Assign(
                targets=[target], value=i.context_expr, lineno=node.lineno
            )
            stmts.append(stmt)
        node.body = stmts + node.body
        ret = create_ast_block(body=node.body, at_node=node)
        # Hint to UnpackScopeRewriter below to leave the new scope alone
        ret.unpack = False
        return ret