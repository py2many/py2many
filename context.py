import ast
from contextlib import contextmanager


def add_variable_context(node):
    """Provide context to Module and Function Def"""
    return VariableTransformer().visit(node)


def add_scope_context(node):
    """Provide to scope context to all nodes"""
    return ScopeTransformer().visit(node)


class ScopeMixin:
    """
    Adds a scope property with the current scope (function, module, for loop)
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
        scopes = [ast.Module, ast.FunctionDef, ast.For, ast.If, ast.With]
        return len([s for s in scopes if isinstance(node, s)]) > 0


class ScopeTransformer(ast.NodeTransformer, ScopeMixin):
    """
    Adds a scope attribute to each node.
    The scope contains the current scope (function, module, for loop)
    a node is part of.
    """

    def visit(self, node):
        with self.enter_scope(node):
            node.scope = self.scope
            return super(ScopeTransformer, self).visit(node)


class VariableTransformer(ast.NodeTransformer, ScopeMixin):
    """Adds all defined variables to scope block"""
    def visit_FunctionDef(self, node):
        node.vars = [a for a in node.args.args]
        self.generic_visit(node)
        return node

    def visit_If(self, node):
        node.vars = []
        map(self.visit, node.body)
        node.body_vars = node.vars

        node.vars = []
        map(self.visit, node.orelse)
        node.orelse_vars = node.vars

        node.vars = []
        return node

    def visit_For(self, node):
        node.vars = [node.target]
        self.generic_visit(node)
        return node

    def visit_Module(self, node):
        node.vars = []
        self.generic_visit(node)
        return node

    def visit(self, node):
        with self.enter_scope(node):
            return super(VariableTransformer, self).visit(node)

    def visit_Assign(self, node):
        new_vars = [t for t in node.targets if isinstance(t.ctx, ast.Store)]
        self.scope.vars += new_vars
        return node
