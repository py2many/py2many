import ast
from contextlib import contextmanager

from py2many.analysis import get_id


def add_scope_context(node):
    """Provide to scope context to all nodes"""
    return ScopeTransformer().visit(node)


class ScopeMixin(object):
    """
    Adds a scope property with the current scope (function, module)
    a node is part of.
    """

    scopes = []

    @contextmanager
    def enter_scope(self, node):
        if self._is_scopable_node(node):
            self.scopes.append(node)
            yield
            self.scopes.pop()
        else:
            yield

    @property
    def scope(self):
        try:
            return self.scopes[-1]
        except IndexError:
            return None

    def _is_scopable_node(self, node):
        scopes = [ast.Module, ast.ClassDef, ast.FunctionDef, ast.For, ast.If, ast.With, ast.Try]
        return len([s for s in scopes if isinstance(node, s)]) > 0


class ScopeList(list):
    """
    Wraps around list of scopes and provides find method for finding
    the definition of a variable
    """

    def find(self, lookup):
        """Find definition of variable lookup."""

        def find_definition(scope, var_attr="vars"):
            for var in getattr(scope, var_attr):
                id = get_id(var)
                if id and id == lookup:
                    return var

        for scope in reversed(self):
            defn = None
            if not defn and hasattr(scope, "vars"):
                defn = find_definition(scope, "vars")
            if not defn and hasattr(scope, "body_vars"):
                defn = find_definition(scope, "body_vars")
            if not defn and hasattr(scope, "orelse_vars"):
                defn = find_definition(scope, "orelse_vars")
            if not defn and hasattr(scope, "body"):
                defn = find_definition(scope, "body")
            if defn:
                return defn

    def find_import(self, lookup):
        for scope in reversed(self):
            if hasattr(scope, "imports"):
                for imp in scope.imports:
                    if imp.name == lookup:
                        return imp

    @property
    def parent_scopes(self):
        scopes = list(self)
        scopes.pop()
        return ScopeList(scopes)


class ScopeTransformer(ast.NodeTransformer, ScopeMixin):
    """
    Adds a scope attribute to each node.
    The scope contains the current scope (function, module, for loop)
    a node is part of.
    """

    def __init__(self) -> None:
        super().__init__()
        self._scope_header = False
        self._named_expr = False

    def visit(self, node):
        with self.enter_scope(node):
            node.scopes = ScopeList(self.scopes)
            if self._scope_header and not self._named_expr and len(node.scopes) > 1:
                node.scopes = ScopeList(self.scopes[:-1])
            return super().visit(node)

    def visit_If(self, node: ast.If):
        self.generic_visit(node.test)
        self._generic_body_visit(node)
        self._scope_header = True
        self.visit(node.test)
        self._scope_header = False
        return node

    def visit_While(self, node: ast.While):
        self._generic_body_visit(node)
        self._scope_header = True
        self.visit(node.test)
        self._scope_header = False
        return node

    def visit_For(self, node: ast.For):
        self.visit(node.target)
        self._generic_body_visit(node)
        self._scope_header = True
        self.visit(node.iter)
        self._scope_header = False
        return node

    def visit_With(self, node: ast.With):
        for n in node.body:
            self.visit(n)
        for item in node.items:
            if item.optional_vars:
                self.visit(item.optional_vars)
        self._scope_header = True
        for item in node.items:
            self.visit(item.context_expr)
        self._scope_header = False
        return node
    
    def visit_Try(self, node: ast.Try):
        for n in node.body:
            self.visit(n)
        for h in node.handlers:
            self.visit(h)
        for oe in node.orelse:
            self.visit(oe)
        for f in node.finalbody:
            self.visit(f)
        return node

    def _generic_body_visit(self, node):
        for n in node.body:
            self.visit(n)
        for oe in node.orelse:
            self.visit(oe)

    def visit_NamedExpr(self, node: ast.NamedExpr):
        self.visit(node.value)
        self._named_expr = True
        self.visit(node.target)
        self._named_expr = False
        return node
