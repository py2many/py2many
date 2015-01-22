import ast
from contextlib import contextmanager


def add_variable_context(node):
    """Provide context to Module and Function Def"""
    return VariableTransformer().visit(node)


def add_scopes(node):
    """Provide to scope context to all nodes"""
    return ScopeTransformer().visit(node)


class ScopeMixin:
    scopes = []

    @contextmanager
    def enter_scope(self, node):
        """Add latest scope to stack and pop it later"""
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
        scopes = [ast.Module, ast.FunctionDef, ast.For, ast.If]
        return len([s for s in scopes if isinstance(node, s)]) > 0


class ScopeTransformer(ast.NodeTransformer, ScopeMixin):
    """Adds parent block to each node as scope"""
    def _is_scopable_node(self, node):
        scopes = [ast.Module, ast.FunctionDef, ast.For]
        return len([s for s in scopes if isinstance(node, s)]) > 0

    def visit(self, node):
        with self.enter_scope(node):
            node.scope = self.scope
            return super(ScopeTransformer, self).visit(node)


class VariableTransformer(ast.NodeTransformer, ScopeMixin):
    """Adds assignment information to For, FunctionDef and Module nodes"""
    def visit_FunctionDef(self, node):
        node.vars = [a for a in node.args.args]
        self.generic_visit(node)
        return node

    def visit_If(self, node):
        node.vars = []
        self.generic_visit(node)
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
