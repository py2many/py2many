import ast

from common.clike import CLikeTranspiler as CommonCLikeTranspiler


class CLikeTranspiler(CommonCLikeTranspiler):
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
