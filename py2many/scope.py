import ast
from collections.abc import Iterable
from contextlib import contextmanager

from py2many.analysis import get_id


def add_scope_context(node):
    """Provide to scope context to all nodes"""
    return ScopeTransformer().visit(node)


class ScopeMixin:
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
        scopes = [
            ast.Module,
            ast.ClassDef,
            ast.FunctionDef,
            ast.Lambda,
            ast.For,
            ast.If,
            ast.With,
        ]
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
                if get_id(var) == lookup:
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
                # special case lambda functions here. Their body is not a list
                if isinstance(scope.body, Iterable):
                    defn = find_definition(scope, "body")
                else:
                    return None
            if defn:
                return defn

    def find_import(self, lookup):  # pragma: no cover
        """
        Find definition of an import.

        Currently unused.
        """
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

    def visit(self, node):
        with self.enter_scope(node):
            node.scopes = ScopeList(self.scopes)
            return super().visit(node)
