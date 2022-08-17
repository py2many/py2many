import ast
from pathlib import PosixPath

from py2many.ast_helpers import get_id
from py2many.tracer import is_list_assignment
from .scope import ScopeMixin


def add_list_calls(node):
    """Provide context to Module and Function Def"""
    return ListCallTransformer().visit(node)


def add_variable_context(node, trees):
    """Provide context to Module and Function Def"""
    return VariableTransformer(trees).visit(node)


def add_assignment_context(node):
    """Annotate nodes on the LHS of an assigment"""
    return LHSAnnotationTransformer().visit(node)


class ListCallTransformer(ast.NodeTransformer):
    """
    Adds all calls to list to scope block.
    You need to apply VariableTransformer before you use it.
    """

    def visit_Call(self, node):
        if self.is_list_addition(node):
            var = node.scopes.find(node.func.value.id)
            if var is not None and is_list_assignment(var.assigned_from):
                if not hasattr(var, "calls"):
                    var.calls = []
                var.calls.append(node)
        return node

    def is_list_addition(self, node):
        """Check if operation is adding something to a list"""
        list_operations = ["append", "extend", "insert"]
        return (
            hasattr(node.func, "ctx")
            and isinstance(node.func.ctx, ast.Load)
            and hasattr(node.func, "value")
            and isinstance(node.func.value, ast.Name)
            and hasattr(node.func, "attr")
            and node.func.attr in list_operations
        )


class VariableTransformer(ast.NodeTransformer, ScopeMixin):
    """Adds all defined variables to scope block"""

    def __init__(self, trees):
        super().__init__()
        self._basedir = None
        if len(trees) == 1:
            self._trees = {}
        else:
            # Identify modules by their full path
            self._trees = {self._parse_path(t.__file__): t for t in trees}
        self._class_vars = []

    def _parse_path(self, path: PosixPath):
        parts = list(path.parts)
        # remove file extension
        parts[-1] = parts[-1].split(".")[0]
        return ".".join(parts)

    def visit_FunctionDef(self, node):
        node.vars = []
        # So function signatures are accessible even after they're
        # popped from the scope
        self.scopes[-2].vars.append(node)
        for arg in node.args.args:
            arg.assigned_from = node
            node.vars.append(arg)

        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node):
        node.vars = []
        # So classes are accessible even after they're
        # popped from the scope
        self.scopes[-2].vars.append(node)
        self._class_vars = []
        self.generic_visit(node)
        if self._class_vars:
            node.vars.extend(self._class_vars)
            self._class_vars = []
        return node

    def visit_Import(self, node):
        for name in node.names:
            name.imported_from = node
        return node

    def visit_ImportFrom(self, node):
        module_path = node.module
        names = [n.name for n in node.names]
        if module_path in self._trees:
            m = self._trees[module_path]
            if hasattr(m, "scopes"):
                resolved_names = [m.scopes.find(n) for n in names]
                node.scopes[-1].vars += resolved_names
        else:
            mod_path_str = ""
            if node.module:
                mod_path = node.module.split(".")
                base_dir = self._basedir.stem if self._basedir else ""
                if mod_path[0] == base_dir:
                    mod_path = mod_path[1:]
                mod_path_str = ".".join(mod_path)
            # Names can also be modules
            for n in names:
                name = f"{mod_path_str}.{n}"
                if name in self._trees and \
                        hasattr((m := self._trees[name]), "scopes"):
                    # Get all the variables defined in the global scope
                    node.scopes[-1].vars.extend(m.scopes[-1].vars)
                elif n in self._trees and \
                        hasattr((m := self._trees[n]), "scopes"):
                    # Get all the variables defined in the global scope
                    node.scopes[-1].vars.extend(m.scopes[-1].vars)

        return node

    def visit_If(self, node):
        node.vars = []
        self.visit(node.test)
        for e in node.body:
            self.visit(e)
        node.body_vars = node.vars

        node.vars = []
        for e in node.orelse:
            self.visit(e)
        node.orelse_vars = node.vars

        node.vars = []
        return node

    def visit_For(self, node: ast.For):
        node.target.assigned_from = node
        if isinstance(node.target, ast.Name):
            node.vars = [node.target]
        elif isinstance(node.target, ast.Tuple):
            node.vars = [*node.target.elts]
        else:
            node.vars = []
        self.generic_visit(node)
        return node

    def visit_While(self, node: ast.While):
        node.vars = []
        self.generic_visit(node)
        return node

    def visit_Module(self, node):
        node.vars = []
        self._basedir = getattr(node, "__basedir__", None)
        self.generic_visit(node)
        return node

    def visit_With(self, node):
        node.vars = []
        self.generic_visit(node)
        return node

    def visit(self, node):
        with self.enter_scope(node):
            return super().visit(node)

    def visit_Assign(self, node):
        for target in node.targets:
            self._generic_target_visit(node, target)
        return node

    def visit_AnnAssign(self, node):
        self._generic_target_visit(node, node.target)
        return node

    def visit_AugAssign(self, node):
        self._generic_target_visit(node, node.target)
        return node

    def _generic_target_visit(self, node, target):
        target.assigned_from = node
        if isinstance(target, ast.Name):
            self.scope.vars.append(target)
        if isinstance(target, ast.Attribute):
            if get_id(target.value) == "self":
                self_var = ast.Name(id=target.attr)
                self_var.target_node = target
                self._class_vars.append(self_var)
            else:
                self_var = target
        if isinstance(target, ast.Tuple) or isinstance(target, ast.List):
            self.scope.vars.extend([t for t in target.elts])


class LHSAnnotationTransformer(ast.NodeTransformer):
    def __init__(self):
        super().__init__()
        self._lhs = False

    def visit(self, node):
        if self._lhs:
            node.lhs = self._lhs
        return super().visit(node)

    def visit_Assign(self, node):
        for target in node.targets:
            self._lhs = True
            self.visit(target)
            self._lhs = False
        self.visit(node.value)
        return node

    def visit_AnnAssign(self, node):
        self._lhs = True
        self.visit(node.target)
        self._lhs = False
        self.visit(node.annotation)
        if node.value is not None:
            self.visit(node.value)
        return node

    def visit_AugAssign(self, node):
        self._lhs = True
        self.visit(node.target)
        self._lhs = False
        self.visit(node.op)
        self.visit(node.value)
        return node
