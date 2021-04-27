import ast

from py2many.analysis import get_id


def detect_mutable_vars(node):
    return MutabilityTransformer().visit(node)


class MutabilityTransformer(ast.NodeTransformer):
    """
    Analyzes every function for mutable variables and put them into FunctionDef node
    """

    def __init__(self):
        self.var_usage_count = {}
        self.lvalue = False

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
        old = self.lvalue
        self.lvalue = True
        target = node.targets[0]
        if isinstance(target, ast.Tuple):
            for e in target.elts:
                self.visit(e)
        self.visit(target)
        self.lvalue = old
        self.generic_visit(node)
        return node

    def visit_AugAssign(self, node):
        old = self.lvalue
        self.lvalue = True
        self.visit(node.target)
        self.lvalue = old
        self.generic_visit(node)
        return node

    def visit_AnnAssign(self, node):
        old = self.lvalue
        self.lvalue = True
        self.visit(node.target)
        self.lvalue = old
        self.generic_visit(node)
        return node

    def visit_Subscript(self, node):
        self.visit(node.value)
        self.visit(node.slice)
        return node

    def visit_Name(self, node):
        if self.lvalue:
            self.increase_use_count(get_id(node))
        return node

    def visit_Call(self, node):
        fname = get_id(node.func)
        fndef = node.scopes.find(fname)
        if fndef and hasattr(fndef, "args"):
            for fnarg, node_arg in zip(fndef.args.args, node.args):
                if hasattr(fndef, "mutable_vars") and fnarg.arg in fndef.mutable_vars:
                    self.increase_use_count(get_id(node_arg))
        if hasattr(node.func, "attr"):
            if node.func.attr == "append":
                self.increase_use_count(get_id(node.func.value))
        self.generic_visit(node)
        return node
