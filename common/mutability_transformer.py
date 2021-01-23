import ast

from common.analysis import get_id


def detect_mutable_vars(node):
    return MutabilityTransformer().visit(node)


class MutabilityTransformer(ast.NodeTransformer):
    """
    Analyzes every function for mutable variables and put them into FunctionDef node
    """

    def __init__(self):
        self.var_usage_count = {}

    def increase_use_count(self, name):
        if not name in self.var_usage_count:
            self.var_usage_count[name] = 0
        self.var_usage_count[name] += 1

    def visit_FunctionDef(self, node):
        self.var_usage_count = {}
        self.generic_visit(node)
        mutable_vars = []
        for var, count in self.var_usage_count.items():
            if count > 1:
                mutable_vars.append(var)
        node.mutable_vars = mutable_vars
        return node

    def visit_Assign(self, node):
        target = node.targets[0]
        self.increase_use_count(get_id(target))
        self.generic_visit(node)
        return node

    def visit_AugAssign(self, node):
        target = node.target
        self.increase_use_count(get_id(target))
        self.generic_visit(node)
        return node

    def visit_AnnAssign(self, node):
        target = node.target
        self.increase_use_count(get_id(target))
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        if hasattr(node.func, "attr"):
            if node.func.attr == "append":
                self.increase_use_count(get_id(node.func.value))
        self.generic_visit(node)
        return node
