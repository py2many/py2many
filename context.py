import ast
from contextlib import contextmanager


def add_imports(node):
    """Provide context of imports Module"""
    return ImportTransformer().visit(node)


def add_list_calls(node):
    """Provide context to Module and Function Def"""
    return ListCallTransformer().visit(node)


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


class ScopeList(list):
    def find(self, lookup):
        for scope in reversed(self):
            for var in scope.vars:
                if (isinstance(var, ast.alias) and var.name == lookup) or \
                   (var.id == lookup):
                    return var

    def find_import(self, lookup):
        for scope in reversed(self):
            if hasattr(scope, "imports"):
                for imp in scope.imports:
                    if imp.name == lookup:
                        return imp


class ScopeTransformer(ast.NodeTransformer, ScopeMixin):
    """
    Adds a scope attribute to each node.
    The scope contains the current scope (function, module, for loop)
    a node is part of.
    """

    def visit(self, node):
        with self.enter_scope(node):
            node.scopes = ScopeList(self.scopes)
            return super(ScopeTransformer, self).visit(node)


class ListCallTransformer(ast.NodeTransformer):
    """
    Adds all calls to list to scope block.
    You need to apply VariableTransformer before you use it.
    """
    def visit_Call(self, node):
#        import pytest; pytest.set_trace()
        if self.is_list_addition(node):
            var = node.scopes.find(node.func.value.id)
            if self.is_list_assignment(var.assigned_from):
                if not hasattr(var, "calls"):
                    var.calls = []
                var.calls.append(node)
        return node

    def is_list_assignment(self, node):
        return (isinstance(node.value, ast.List) and
                isinstance(node.targets[0].ctx, ast.Store))

    def is_list_addition(self, node):
        """Check if operation is adding something to a list"""
        list_operations = ["append", "extend", "insert"]
        return (isinstance(node.func.ctx, ast.Load) and
                hasattr(node.func, "value") and
                isinstance(node.func.value, ast.Name) and
                node.func.attr in list_operations)


class ImportTransformer(ast.NodeTransformer):
    """Adds imports to scope block"""
    def visit_Import(self, node):
        for name in node.names:
            name.imported_from = node
            name.scopes[-1].imports.append(name)

    def visit_Module(self, node):
        node.imports = []
        self.generic_visit(node)
        return node


class VariableTransformer(ast.NodeTransformer, ScopeMixin):
    """Adds all defined variables to scope block"""
    def visit_FunctionDef(self, node):
        node.vars = []
        for arg in node.args.args:
            arg.assigned_from = node
            node.vars.append(arg)
        self.generic_visit(node)
        return node

    def visit_Import(self, node):
        for name in node.names:
            name.imported_from = node

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
        node.target.assigned_from = node
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
        for target in node.targets:
            target.assigned_from = node
            self.scope.vars.append(target)
        return node
