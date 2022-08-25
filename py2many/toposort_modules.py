import ast
from pathlib import Path, PosixPath, WindowsPath
import sys
from toposort import toposort_flatten
from collections import defaultdict
from typing import Tuple


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
        # Consider import_from level
        module_path = node.module
        if node.level >= 1:
            # get path (excluding name of the file)
            path = self._filename.as_posix().split("/")[:-node.level]
            path_str = ".".join(path)
            module_path = f"{path_str}.{module_path}" if path_str else module_path

        if module_path in self._modules:
            self.deps[self._current].add(module_path)
        # Names can also be modules
        mod_path_str = ""
        if module_path:
            mod_path = module_path.split(".")
            base_dir = self._basedir.stem if self._basedir else ""
            if mod_path[0] == base_dir:
                mod_path = mod_path[1:]
            mod_path_str = ".".join(mod_path)
        names = [alias.name for alias in node.names]
        for name in names:
            mod_name = f"{mod_path_str}.{name}"
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
