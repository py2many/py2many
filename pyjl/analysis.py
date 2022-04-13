
import ast
from distutils.log import warn
import logging
from typing import Any

from py2many.ast_helpers import get_id
from py2many.tracer import find_in_scope

logger = logging.Logger("pyjl")

def analyse_loops(node, extension=False):
    visitor = JuliaLoopAnalysis()
    visitor.visit(node)


class JuliaLoopAnalysis(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._loop_targets = set()
        self._targets_out_of_scope = set()
        self._assign_targets = set()
        self._loop_scope = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._targets_out_of_scope = set()
        self._generic_scope_analysis(node)

        if len(self._targets_out_of_scope) == 1:
            if target := self._targets_out_of_scope.pop():
                warn(f"\033[93mWARNING { node.__file__.name}: Loop target variable(s)"
                     f" '{get_id(target)}' is used outside the scope of the loop"
                     f" on line {target.lineno}\033[0m")
        elif len(self._targets_out_of_scope) > 1:
            linenos = map(lambda x: x.lineno, self._targets_out_of_scope)
            elems = []
            for target, lineno in zip(self._targets_out_of_scope, linenos):
                if target_id := get_id(target):
                    elems.append(f"- {target_id} on linenumber {lineno}")
            elems_str = "\n".join(elems)
            logger.warn(f"\033[93mWARNING { node.__file__.name}: Loop target variables"
                 f" outside the scope of the loop:\n"
                 f"{elems_str}\033[0m")
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_analysis(node)
        return node

    def _generic_scope_analysis(self, node):
        self._assign_targets = set()
        self._loop_targets = set()
        self._loop_scope = False

        self.generic_visit(node)

        if self._assign_targets:
            target_ids = map(get_id, self._targets_out_of_scope)
            temp = set()
            for t_id, t in zip(target_ids, self._targets_out_of_scope):
                if t_id in self._assign_targets:
                    temp.add(t)
            self._targets_out_of_scope.difference_update(temp)

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        if not self._loop_scope and \
                get_id(node) in self._loop_targets:
            self._targets_out_of_scope.add(node)
        return node

    def visit_arg(self, node: ast.arg) -> Any:
        self.generic_visit(node)
        if not self._loop_scope and \
                node.arg in self._loop_targets:
            self._targets_out_of_scope.add(node)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self.generic_visit(node)
        if not isinstance(node.slice, ast.Slice) \
                and node.slice in self._loop_targets \
                and self._loop_scope:
            self._targets_out_of_scope.add(node.slice)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)

        if not self._loop_scope:
            # Verify pre-condition
            for t in node.targets:
                targets = self._get_target(t)
                self._assign_targets.update(targets)                    

        return node

    # TODO: Is this efficient?
    def visit_If(self, node: ast.If) -> Any:
        self.visit(node.test)

        # Visit body
        ## Create backup
        backup_loop_state = self._loop_targets.copy()
        backup_assign_state = self._assign_targets.copy()
        for n in node.body:
            self.visit(n)
        ## Save state
        saved_loop_state = self._loop_targets.copy()
        saved_assign_state = self._assign_targets.copy()
        ## Restore backup
        self._loop_targets.intersection_update(backup_loop_state)
        self._assign_targets.intersection_update(backup_assign_state)

        # Visit orelse
        for oe in node.orelse:
            self.visit(oe)
        ## Join with saved state
        self._loop_targets.update(saved_loop_state)
        self._assign_targets.update(saved_assign_state)

        return node

    def visit_For(self, node: ast.For) -> Any:
        targets = self._get_target(node.target)
        self._loop_targets.update(targets)
        self._loop_scope = True

        # Support nested loops
        for n in node.body:
            if isinstance(n, ast.For):
                n.is_nested_loop = True

        self.generic_visit(node)
        if not getattr(node, "is_nested_loop", None):
            self._loop_scope = False

        return node

    def _get_target(self, target):
        if id := get_id(target):
            return {id}
        elif isinstance(target, ast.Tuple) or \
                isinstance(target, ast.List):
            set_elems = set()
            for e in target.elts:
                set_elems.update(self._get_target(e))
            return set_elems

        return set()