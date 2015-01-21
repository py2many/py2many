import ast


def add_variable_context(node):
    """Provide context to Module and Function Def"""
    return ModuleContextTransformer().visit(node)


class ModuleContextTransformer(ast.NodeTransformer):
    def __init__(self):
        super(ModuleContextTransformer, self).__init__()
        self._global_vars = []
        self._local_vars = []
        self._function_stack = []

    def visit_FunctionDef(self, node):
        self._function_stack.append(node)
        self.generic_visit(node)
        self._local_vars.extend(node.args.args)

        node.context = self._local_vars
        self._local_vars = []

        return node

    def visit_Module(self, node):
        node.context = self._global_vars
        self.generic_visit(node)
        return node

    def visit_Assign(self, node):
        new_vars = [t for t in node.targets if isinstance(t.ctx, ast.Store)]
        if(len(self._function_stack) > 0):
            self._local_vars.extend(new_vars)
        else:
            self._global_vars.extend(new_vars)
        return node
