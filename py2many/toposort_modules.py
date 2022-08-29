import ast
from pathlib import Path, PosixPath, WindowsPath
import sys
from toposort import toposort_flatten
from collections import defaultdict
from typing import Tuple

from py2many.helpers import get_import_module_name


def module_for_path(path: Path) -> str:
    # strip out .py at the end
    module = ".".join(path.parts)
    return module.rsplit(".", 1)[0]


class ImportDependencyVisitor(ast.NodeVisitor):
    def __init__(self, modules):
        self.deps = defaultdict(set)
        self._modules = modules
        self._basedir = None
        self._filename = None

    def visit_Module(self, node):
        self._current = module_for_path(node.__file__)
        self._basedir = getattr(node, "__basedir__", None)
        self._filename = getattr(node, "__file__", None)
        self.generic_visit(node)

    def visit_ImportFrom(self, node):
        # Get module path
        module_path = get_import_module_name(node, self._filename, self._basedir)
        if module_path in self._modules:
            self.deps[self._current].add(module_path)
        # Names can also be modules
        names = [alias.name for alias in node.names]
        for name in names:
            mod_name = f"{module_path}.{name}"
            if name in self._modules:
                self.deps[self._current].add(name)
            elif mod_name in self._modules:
                self.deps[self._current].add(mod_name)
        self.generic_visit(node)

    def visit_Import(self, node):
        names = [n.name for n in node.names]
        for n in names:
            if n in self._modules:
                self.deps[self._current].add(n)
        self.generic_visit(node)


def get_dependencies(trees):
    modules = {module_for_path(node.__file__) for node in trees}
    visitor = ImportDependencyVisitor(modules)
    for t in trees:
        visitor.visit(t)
    for m in modules:
        if m not in visitor.deps:
            visitor.deps[m] = set()
    return visitor.deps


def toposort(trees) -> Tuple:
    deps = get_dependencies(trees)
    tree_dict = {module_for_path(node.__file__): node for node in trees}
    return tuple([tree_dict[t] for t in toposort_flatten(deps, sort=True)])
