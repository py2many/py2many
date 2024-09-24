import ast

from .ast_helpers import get_id

get_id  # quiten pyflakes; this should when code is updated to use ast_helpers

IGNORED_MODULE_SET = {
    "typing",
    "enum",
    "dataclasses",
    "ctypes",
    "math",
    "__future__",
    "asyncio",
    "sys",
    "os",
    "adt",
    "py2many.result",
    "py2many.smt",
}


def add_imports(node):
    """Provide context of imports Module"""
    return ImportTransformer().visit(node)


def is_void_function(fun):
    finder = ReturnFinder()
    finder.visit(fun)
    return not (finder.returns or fun.returns is not None)


def is_global(target):
    return isinstance(target.scopes[-1], ast.Module)


def is_mutable(scopes, target):
    for scope in scopes:
        if isinstance(scope, ast.FunctionDef):
            if target in scope.mutable_vars:
                return True
    return False


def is_ellipsis(node):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Constant)
        and node.value.value == ...
    )


class ReturnFinder(ast.NodeVisitor):
    returns = False

    def visit_Return(self, node):
        if node.value != None:
            self.returns = True


class FunctionTransformer(ast.NodeTransformer):
    """Tracks defined functions in scope"""

    def visit_FunctionDef(self, node):
        node.defined_functions = []
        node.scopes[-2].defined_functions.append(node)
        self.generic_visit(node)
        return node

    def _visit_Scoped(self, node):
        node.defined_functions = []
        self.generic_visit(node)
        return node

    def visit_Module(self, node):
        return self._visit_Scoped(node)

    def visit_ClassDef(self, node):
        return self._visit_Scoped(node)

    def visit_For(self, node):
        return self._visit_Scoped(node)

    def visit_If(self, node):
        return self._visit_Scoped(node)

    def visit_With(self, node):
        return self._visit_Scoped(node)

    def visit_ImportFrom(self, node):
        for name in node.names:
            if node.module not in IGNORED_MODULE_SET:
                node.scopes[-1].defined_functions.append(name)
        return node


class CalledWithTransformer(ast.NodeTransformer):
    """
    Tracks whether variables or functions get
    used as arguments of other functions
    """

    def visit_Assign(self, node):
        for target in node.targets:
            target.called_with = []
        return node

    def visit_FunctionDef(self, node):
        node.called_with = []
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        for arg in node.args:
            if isinstance(arg, ast.Name):
                var = node.scopes.find(arg.id)
                var.called_with.append(node)
        self.generic_visit(node)
        return node


class AttributeCallTransformer(ast.NodeTransformer):
    """Tracks attribute function calls on variables"""

    def visit_Assign(self, node):
        for target in node.targets:
            target.calls = []
        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Attribute):
            var = node.scopes.find(node.func.value.id)
            var.calls.append(node)
        return node


class ImportTransformer(ast.NodeTransformer):
    """Adds imports to scope block"""

    def visit_ImportFrom(self, node):
        for name in node.names:
            name.imported_from = node
            scope = name.scopes[-1]
            if hasattr(scope, "imports"):
                scope.imports.append(name)
        return node

    def visit_Module(self, node):
        node.imports = []
        self.generic_visit(node)
        return node
