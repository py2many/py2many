import ast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node


class ZigImplicitConstructor(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node):
        needs_init = "dataclass" not in [get_id(n) for n in node.decorator_list]
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                if b.name == "__init__":
                    needs_init = False

        if not needs_init:
            return node

        new_node = create_ast_node("def __init__(self): pass")
        ast.fix_missing_locations(new_node)
        node.body.insert(0, new_node)
        return node


class ZigErrorUnionAnalyzer(ast.NodeTransformer):
    """Analyzes functions to determine if they need error union return types (!void or !T)"""

    def __init__(self):
        super().__init__()

    def visit_FunctionDef(self, node):
        # Initialize needs_error_type to False if not already set
        if not hasattr(node, "needs_error_type"):
            node.needs_error_type = False
        self.generic_visit(node)
        return node

    def visit_Assert(self, node):
        """Mark containing function as needing error type when assert is found"""
        fndef = self._find_containing_function(node)
        if fndef:
            fndef.needs_error_type = True
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        """Mark containing function as needing error type when error-prone call is found"""
        # Check if it's a function call that might need try
        if hasattr(node, "result_type") or hasattr(node.func, "result_type"):
            fndef = self._find_containing_function(node)
            if fndef:
                fndef.needs_error_type = True
        self.generic_visit(node)
        return node

    def _find_containing_function(self, node):
        """Find the containing function definition for a given node"""
        if hasattr(node, "scopes"):
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    return scope
        return None


class ZigInferMoveSemantics(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_arg(self, node):
        node.is_arg = True
        return node

    def visit_Return(self, node):
        if node.value:
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                definition = node.scopes.find(get_id(node.value))
                if definition is None:
                    for arg in fndef.args.args:
                        if get_id(node.value) == get_id(arg):
                            definition = arg
                            break
                if definition and getattr(definition, "is_arg", None):
                    node.transfer = True
                    definition.owned = True
        return node
