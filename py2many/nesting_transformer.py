import ast


def detect_nesting_levels(node):
    return NestingTransformer().visit(node)


class NestingTransformer(ast.NodeTransformer):
    """
    Some languages are white space sensitive. This transformer
    annotates relevant nodes with the nesting level
    """

    def __init__(self):
        self.level = 0

    def _visit_level(self, node) -> ast.AST:
        node.level = self.level
        self.level += 1
        self.generic_visit(node)
        self.level -= 1
        return node

    def visit_FunctionDef(self, node):
        return self._visit_level(node)

    def visit_ClassDef(self, node):
        return self._visit_level(node)

    def visit_If(self, node):
        return self._visit_level(node)

    def visit_While(self, node):
        return self._visit_level(node)

    def visit_For(self, node):
        return self._visit_level(node)

    def visit_Assign(self, node):
        node.level = self.level
        self.generic_visit(node)
        return node
