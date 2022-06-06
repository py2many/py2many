
import ast
import logging
from typing import Any, Dict

from py2many.ast_helpers import get_id

logger = logging.Logger("pyjl")


def analyse_loop_scope(node, extension=False):
    visitor = JuliaLoopScopeAnalysis()
    visitor.visit(node)


def optimize_loop_ranges(node, extension=False):
    visitor = JuliaLoopRangesOptimization()
    visitor.visit(node)


def get_target(target):
    if id := get_id(target):
        return {id}
    elif isinstance(target, ast.Tuple) or \
            isinstance(target, ast.List):
        set_elems = set()
        for e in target.elts:
            set_elems.update(get_target(e))
        return set_elems

    return set()


class JuliaLoopScopeAnalysis(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._loop_targets = set()
        self._targets_out_of_scope: Dict[str, Any] = {}
        self._assign_targets = set()
        self._loop_scope = False
        self._ignore_vars = []

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "optimize_loop_target", False) or \
                getattr(node, "loop_scope_warning", False):
            self._targets_out_of_scope = {}
            self._generic_scope_analysis(node)
            if getattr(node, "loop_scope_warning", False):
                self._emit_warning(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_analysis(node)
        return node

    # TODO: Maybe set as an event?
    def _emit_warning(self, node):
        if self._targets_out_of_scope:
            elems = []
            for t_id, target in self._targets_out_of_scope.items():
                elems.append(f"- {t_id} on linenumber {target.lineno}")
            elems_str = "\n".join(elems)
            logger.warn(f"\033[93mWARNING { node.__file__.name}: Loop target variables"
                        f" outside the scope of the loop:\n"
                        f"{elems_str}\033[0m")

    def _generic_scope_analysis(self, node):
        self._assign_targets = set()
        self._loop_targets = set()
        self._loop_scope = False
        self._ignore_vars = []

        self.generic_visit(node)

        # TODO: I know, it looks bad
        if self._assign_targets:
            temp = []
            for t_id, t in self._targets_out_of_scope.items():
                if t_id in self._assign_targets or \
                        t_id in self._ignore_vars:
                    temp.append(t_id)
            for t in temp:
                self._targets_out_of_scope.pop(t)

        node.targets_out_of_scope = self._targets_out_of_scope.keys()

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        id = get_id(node)
        if not self._loop_scope and \
                id in self._loop_targets:
            self._targets_out_of_scope[id] = node
        return node

    def visit_arg(self, node: ast.arg) -> Any:
        self.generic_visit(node)
        if not self._loop_scope and \
                node.arg in self._loop_targets:
            self._targets_out_of_scope[node.arg] = node
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)

        if not self._loop_scope:
            # Verify pre-condition
            for t in node.targets:
                targets = get_target(t)
                self._assign_targets.update(targets)

        return node

    # TODO: Is this efficient?
    def visit_If(self, node: ast.If) -> Any:
        self.visit(node.test)

        # Visit body
        # Create backup
        backup_loop_state = self._loop_targets.copy()
        backup_assign_state = self._assign_targets.copy()
        for n in node.body:
            self.visit(n)
        # Save state
        saved_loop_state = self._loop_targets.copy()
        saved_assign_state = self._assign_targets.copy()
        # Restore backup
        self._loop_targets.intersection_update(backup_loop_state)
        self._assign_targets.intersection_update(backup_assign_state)

        # Visit orelse
        for oe in node.orelse:
            self.visit(oe)
        # Join with saved state
        self._loop_targets.update(saved_loop_state)
        self._assign_targets.update(saved_assign_state)

        return node

    def visit_For(self, node: ast.For) -> Any:
        targets = get_target(node.target)
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

    def visit_ListComp(self, node: ast.ListComp) -> Any:
        self.generic_visit(node)
        self._ignore_vars.append(get_id(node.elt))
        return node

    def visit_Lambda(self, node: ast.Lambda) -> Any:
        self.generic_visit(node)
        self._ignore_vars.extend([get_id(x) for x in node.args.args])
        return node


class JuliaLoopRangesOptimization(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._is_subscript = False
        # Analysis phase
        self._loop_targets = set()
        self._non_optimizable_targets = set()
        self._loop_scope = False
        # Marking phase
        self._marking = False
        self._subscript_vars = set()

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "optimize_loop_target", False):
            self.generic_visit(node)
        return node

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        if not self._marking:
            if self._loop_scope and not self._is_subscript and \
                    get_id(node) in self._loop_targets:
                self._non_optimizable_targets.add(get_id(node))
        else:
            if self._is_subscript:
                self._subscript_vars.add(get_id(node))
        return node

    def visit_arg(self, node: ast.arg) -> Any:
        self.generic_visit(node)
        if not self._marking:
            if self._loop_scope and not self._is_subscript and \
                    node.arg in self._loop_targets:
                self._non_optimizable_targets.add(node.arg)
        else:
            if self._is_subscript:
                self._subscript_vars.add(node.arg)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        if self._marking:
            self._is_subscript = True
            self.generic_visit(node)
            self._is_subscript = False
            # Check if any vars are not optimizable
            diff = self._subscript_vars.intersection(self._non_optimizable_targets)
            optimizable = diff == set()
            if isinstance(node.slice, ast.Slice):
                node.slice.range_optimization = optimizable
            node.range_optimization = optimizable
        else:
            self._is_subscript = True
            # Limitation
            self.generic_visit(node)
            self._is_subscript = False
        return node

    def visit_For(self, node: ast.For) -> Any:
        targets = get_target(node.target)

        # Pre-condition: iter can only be a call to range
        if (isinstance(node.iter, ast.Call) and
                get_id(node.iter.func) == "range"):
            # Analysis Phase
            if not getattr(node, "is_nested_loop", None):
                self._non_optimizable_targets = set()
                self._loop_scope = True

            # Update targets
            self._loop_targets.update(targets)

            # Support for nested loops
            for n in node.body:
                if isinstance(n, ast.For):
                    n.is_nested_loop = True
                self.visit(n)

            if not getattr(node, "is_nested_loop", None):
                self._loop_targets = set()
                self._loop_scope = False

            # Add information to iter
            intersection = targets.intersection(self._non_optimizable_targets)
            is_optimizable = intersection == set()
            node.iter.range_optimization = is_optimizable
            # If one variable is not optimizable, the others aren't as well
            if not is_optimizable:
                self._non_optimizable_targets.intersection_update(targets)
        else:
            self._non_optimizable_targets.update(targets)

        # Marking Phase: marking is always executed, to support nested loops
        self._marking = True
        for n in node.body:
            self.visit(n)
        self._marking = False        

        return node
