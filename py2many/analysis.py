import ast
import importlib
from typing import Any

from .ast_helpers import get_id


get_id  # quiten pyflakes; this should when code is updated to use ast_helpers

IGNORED_MODULE_SET = set(
    [
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
    ]
)


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
    """Adds imports to scope block and analyses import names"""

    def __init__(self) -> None:
        super().__init__()
        self._imported_names = {}

    def visit_Import(self, node) -> str:
        for (name, asname), imp_name in zip(self._get_aliases(node.names), node.names):
            self._add_scope_imports(node, imp_name)
            try:
                imported_name = importlib.import_module(name)
            except ImportError:
                imported_name = name
            if asname is not None:
                self._imported_names[asname] = imported_name
            else:
                self._imported_names[name] = imported_name
        return node

    def visit_ImportFrom(self, node) -> str:
        imported_name = node.module
        imported_module = None
        if node.module:
            try:
                imported_module = importlib.import_module(node.module)
            except ImportError:
                pass
        else:
            # Import from '.'
            imported_name = "."

        for (name, asname), imp_name in zip(self._get_aliases(node.names), node.names):
            self._add_scope_imports(node, imp_name)
            asname = asname if asname is not None else name
            if imported_module:
                self._imported_names[asname] = getattr(imported_module, name, None)
            else:
                self._imported_names[asname] = (imported_name, name)
        return node

    def _get_aliases(self, names: list[ast.alias]):
        aliases = []
        for n in names:
            aliases.append((n.name, getattr(n, "asname", None)))
        return aliases

    def _add_scope_imports(self, node, name) -> Any:
        name.imported_from = node
        scope = name.scopes[-1]
        if hasattr(scope, "imports"):
            scope.imports.append(name)

    def visit_Module(self, node):
        self._imported_names = {}
        node.imports = []
        self.generic_visit(node)
        node.imported_names = self._imported_names
        return node

    def visit_If(self, node: ast.If) -> Any:
        node.imports = []
        self.generic_visit(node)
        return node

    def visit_With(self, node: ast.With) -> Any:
        node.imports = []
        self.generic_visit(node)
        return node
