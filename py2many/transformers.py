import ast

from py2many.ast_helpers import get_id


def detect_nesting_levels(node):
    return NestingTransformer().visit(node)


def detect_mutable_vars(node):
    return MutabilityTransformer().visit(node)


def add_annotation_flags(node):
    return AnnotationTransformer().visit(node)


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

    def _visit_assign_target(self, node) -> ast.AST:
        old = self.lvalue
        self.lvalue = True
        self.visit(node.target)
        self.lvalue = old
        self.generic_visit(node)
        return node

    def visit_AugAssign(self, node):
        return self._visit_assign_target(node)

    def visit_AnnAssign(self, node):
        return self._visit_assign_target(node)

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


class AnnotationTransformer(ast.NodeTransformer):
    """
    Adds a flag for every type annotation and nested types so they can be differentiated from array
    """

    def __init__(self):
        self.handling_annotation = False

    def visit_arg(self, node):
        if node.annotation:
            self.handling_annotation = True
            self.visit(node.annotation)
            self.handling_annotation = False
        return node

    def visit_FunctionDef(self, node):
        if node.returns:
            self.handling_annotation = True
            self.visit(node.returns)
            self.handling_annotation = False
        self.generic_visit(node)
        return node

    def _visit_record_handling_annotation(self, node) -> ast.AST:
        if self.handling_annotation:
            node.is_annotation = True
        self.generic_visit(node)
        return node

    # without this Dict[x,y] will be translated to HashMap<(x,y)>
    def visit_Tuple(self, node):
        return self._visit_record_handling_annotation(node)

    def visit_List(self, node):
        return self._visit_record_handling_annotation(node)

    def visit_Name(self, node):
        return self._visit_record_handling_annotation(node)

    def visit_Subscript(self, node):
        return self._visit_record_handling_annotation(node)

    def visit_AnnAssign(self, node):
        self.handling_annotation = True
        self.visit(node.target)
        self.handling_annotation = False
        self.generic_visit(node)
        return node
