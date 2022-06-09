
import ast
import logging
from typing import Any, Dict

from py2many.ast_helpers import get_id

logger = logging.Logger("pyjl")


def analyse_variable_scope(node, extension=False):
    visitor = JuliaVariableScopeAnalysis()
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


class JuliaVariableScopeAnalysis(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._variables_out_of_scope: Dict[str, Any] = {}
        self._scope_vars = set()
        self._assign_targets = set()
        self._ignore_vars = set()
        self._hard_scope = False

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "fix_scope_bounds", False) or \
                getattr(node, "loop_scope_warning", False):
            self._variables_out_of_scope = {}
            self._scope_analysis(node)
            if getattr(node, "loop_scope_warning", False):
                self._emit_warning(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._scope_analysis(node)
        return node

    # TODO: Maybe set as an event?
    def _emit_warning(self, node):
        if self._variables_out_of_scope:
            elems = []
            for t_id, target, _ in self._variables_out_of_scope.items():
                elems.append(f"- {t_id} on linenumber {target.lineno}")
            elems_str = "\n".join(elems)
            logger.warn(f"\033[93mWARNING { node.__file__.name}: Loop target variables"
                        f" outside the scope of the loop:\n"
                        f"{elems_str}\033[0m")

    def _scope_analysis(self, node):
        self._scope_vars = set()
        self._assign_targets = set()
        self._ignore_vars = set()
        self._hard_scope = False

        self.generic_visit(node)

        if self._assign_targets or self._ignore_vars:
            joined_set = self._assign_targets.union(self._ignore_vars)
            for t_id in joined_set:
                if t_id in self._variables_out_of_scope:
                    self._variables_out_of_scope.pop(t_id)
        node.variables_out_of_scope = self._variables_out_of_scope

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        id = get_id(node)
        if not self._hard_scope and \
                id in self._scope_vars:
            ann = self._get_ann(node)
            self._variables_out_of_scope[id] = (node, ann)
        return node

    def visit_arg(self, node: ast.arg) -> Any:
        self.generic_visit(node)
        if not self._hard_scope and \
                node.arg in self._scope_vars:
            ann = self._get_ann(node)
            self._variables_out_of_scope[node.arg] = (node, ann)
        return node
    
    def _get_ann(self, node):
        if hasattr(node, "annotation"):
            return node.annotation
        elif hasattr(node, "scopes"):
            nd = node.scopes.find(get_id(node))
            if hasattr(nd, "annotation"):
                return nd.annotation
        return None

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        for t in node.targets:
            targets = get_target(t)
            if not self._hard_scope:
                # Take into account all assignments performed 
                # outside hard scopes
                self._assign_targets.update(targets)
            else:
                self._scope_vars.update(targets)
        return node
    
    def visit_For(self, node: ast.For) -> Any:
        targets = get_target(node.target)
        self._scope_vars.update(targets)
        return self._generic_scope_visit(node)

    def visit_With(self, node: ast.With) -> Any:
        return self._generic_scope_visit(node)

    def visit_While(self, node: ast.While) -> Any:
        return self._generic_scope_visit(node)

    def visit_If(self, node: ast.If) -> Any:
        self._hard_scope = True
        self.visit(node.test)
        if not getattr(node, "orelse", []):
            for n in node.body:
                self._check_nested(n)
                self.visit(n)
        else:
            # Visit body
            # Create backup
            backup_loop_state = self._scope_vars.copy()
            # backup_assign_state = self._assign_targets.copy()
            for n in node.body:
                self._check_nested(n)
                self.visit(n)
            # Save state
            saved_loop_state = self._scope_vars.copy()
            # saved_assign_state = self._assign_targets.copy()
            # Restore backup
            self._scope_vars.intersection_update(backup_loop_state)
            # self._assign_targets.intersection_update(backup_assign_state)

            # Visit orelse
            for oe in node.orelse:
                self.visit(oe)
            # Join with saved state
            self._scope_vars.update(saved_loop_state)
            # self._assign_targets.update(saved_assign_state)

        return self._generic_scope_visit(node)

    def _generic_scope_visit(self, node) -> Any:
        self._hard_scope = True
        # Support nested loops
        for n in node.body:
            # Find nodes that create their own scopes
            self._check_nested(n)
        self.generic_visit(node)
        if not getattr(node, "is_nested", None):
            self._hard_scope = False

        return node

    def _check_nested(self, node):
        if isinstance(node, (ast.For, ast.While, 
                ast.FunctionDef, ast.With, ast.If)):
            node.is_nested = True

    def visit_ListComp(self, node: ast.ListComp) -> Any:
        self.generic_visit(node)
        self._ignore_vars.add(get_id(node.elt))
        return node

    def visit_Lambda(self, node: ast.Lambda) -> Any:
        self.generic_visit(node)
        self._ignore_vars.update([get_id(x) for x in node.args.args])
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
        if getattr(node, "optimize_loop_ranges", False):
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

            # Visit iter: Currently, if loop target variables are used in 
            # iter, they cannot be optimized, as they might affect range calculations.
            # See tests/performance_tests/sieve/sieve.py for an example.
            self.visit(node.iter)

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
