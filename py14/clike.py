import ast

from common.clike import CLikeTranspiler as CommonCLikeTranspiler

py14_type_map = {
    "bool": "bool",
    "int": "int",
    "float": "double",
    "bytes": "byte[]",
    "str": "string",
}

class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        self._type_map = py14_type_map

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            return "std::pow({0}, {1})".format(
                self.visit(node.left), self.visit(node.right)
            )
        return " ".join(
            [self.visit(node.left), self.visit(node.op), self.visit(node.right)]
        )

    def visit_In(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return "{0}.contains({1})".format(right, left)

    def visit_Constant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        else:
            return str(node.value)
