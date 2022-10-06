
import ast

from py2many.helpers import is_dir


class AnalyseModuleDependencies(ast.NodeTransformer):
    USE_MODULES = False

    def __init__(self) -> None:
        super().__init__()
        self._basedir = None

    def visit_Module(self, node: ast.Module):
        self._basedir = getattr(node, "__basedir__", None)
        self.generic_visit(node)
        return node

    def visit_ImportFrom(self, node: ast.ImportFrom):
        if node.module and is_dir(node.module, self._basedir):
            for alias in node.names:
                name = alias.name
                lookup = f"{node.module}.{name}"
                if is_dir(lookup, self._basedir):
                    self.USE_MODULES = True
        return node


def analyse_module_dependencies(trees):
    visitor = AnalyseModuleDependencies()
    use_modules = False
    for t in trees:
        visitor.visit(t)
        if visitor.USE_MODULES:
            use_modules = True
            break
    if use_modules:
        for t in trees:
            t.use_modules = True
    