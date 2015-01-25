import ast


def add_imports(node):
    """Provide context of imports Module"""
    return ImportTransformer().visit(node)


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

    def visit_Import(self, node):
        for name in node.names:
            node.scopes[-1].defined_functions.append(node)


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
        node.calls = []
        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Attribute):
            var = node.scopes.find(node.func.value.id)
            var.calls.append(node)
        return node


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
