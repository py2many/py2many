import ast
from collections import defaultdict
from pathlib import Path
from typing import Tuple


def module_for_path(path: Path) -> str:
    # strip out .py at the end
    module = ".".join(path.parts)
    return module.rsplit(".", 1)[0]


class ImportDependencyVisitor(ast.NodeVisitor):
    def __init__(self, modules):
        self.deps = defaultdict(set)
        self._modules = modules

    def visit_Module(self, node):
        self._current = module_for_path(node.__file__)
        self.generic_visit(node)

    def visit_ImportFrom(self, node):
        if node.module in self._modules:
            self.deps[self._current].add(node.module)
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


class TopologicalSorter:
    def __init__(self, graph=None):
        self._graph = defaultdict(set)
        self._dependent_nodes = defaultdict(set)
        self._nodes = set()
        if graph:
            for node, predecessors in graph.items():
                self.add(node, *predecessors)

    def add(self, node, *predecessors):
        self._nodes.add(node)
        self._graph[node].update(predecessors)
        for p in predecessors:
            self._nodes.add(p)
            self._dependent_nodes[p].add(node)

    def prepare(self):
        self._in_degree = {node: len(self._graph[node]) for node in self._nodes}
        self._active_nodes = set(self._nodes)

    def is_active(self):
        return bool(self._active_nodes)

    def get_ready(self):
        ready = [node for node in self._active_nodes if self._in_degree[node] == 0]
        if not ready and self._active_nodes:
            # Cycle detected
            ready = [min(self._active_nodes)]
        return tuple(ready)

    def done(self, *nodes):
        for node in nodes:
            if node in self._active_nodes:
                self._active_nodes.remove(node)
                for dependent in self._dependent_nodes[node]:
                    if dependent in self._active_nodes:
                        self._in_degree[dependent] -= 1

    def static_order(self):
        self.prepare()
        while self.is_active():
            node_group = self.get_ready()
            for node in sorted(node_group):
                yield node
            self.done(*node_group)


class StableTopologicalSorter(TopologicalSorter):
    pass


def toposort(trees) -> Tuple:
    deps = get_dependencies(trees)
    tree_dict = {module_for_path(node.__file__): node for node in trees}
    ts = StableTopologicalSorter(deps)
    return tuple([tree_dict[t] for t in ts.static_order()])
