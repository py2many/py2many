import sys
import ast


def add_imports(node):
    """Provide context of imports Module"""
    return ImportTransformer().visit(node)


def is_void_function(fun):
    finder = ReturnFinder()
    finder.visit(fun)
    return not (finder.returns or fun.returns is not None)


if sys.version_info[0] >= 3:

    def get_id(var):
        if isinstance(var, ast.alias):
            return var.name
        elif isinstance(var, ast.Name):
            return var.id
        elif isinstance(var, ast.arg):
            return var.arg
        elif isinstance(var, ast.FunctionDef):
            return var.name
        elif isinstance(var, ast.ClassDef):
            return var.name
        else:
            # print(f"warning: {var}"")
            return None


else:

    def get_id(var):
        if isinstance(var, ast.alias):
            return var.name
        elif isinstance(var, ast.Name):
            return var.id


def is_global(target):
    return isinstance(target.scopes[-1], ast.Module)


def is_mutable(scopes, target):
    for scope in scopes:
        if isinstance(scope, ast.FunctionDef):
            if target in scope.mutable_vars:
                return True
    return False


class ReturnFinder(ast.NodeVisitor):
    returns = False

    def visit_Return(self, node):
        if node.value != None:
            self.returns = True


class FunctionTransformer(ast.NodeTransformer):
    """Tracks defined functions in scope"""

    def visit_Module(self, node):
        node.defined_functions = []
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node):
        node.defined_functions = []
        node.scopes[-2].defined_functions.append(node)
        self.generic_visit(node)
        return node

    def visit_ImportFrom(self, node):
        for name in node.names:
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
