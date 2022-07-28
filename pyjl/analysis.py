
import ast
import logging
import re
from typing import Any, Dict

from py2many.ast_helpers import get_id
from py2many.helpers import get_ann_repr
from pyjl.global_vars import SEP

logger = logging.Logger("pyjl")


def analyse_variable_scope(node, extension=False):
    visitor = JuliaVariableScopeAnalysis()
    visitor.visit(node)


def optimize_loop_ranges(node, extension=False):
    visitor = JuliaLoopRangesOptimization()
    visitor.visit(node)


def detect_broadcast(node, extension=False):
    visitor = JuliaBroadcastTransformer()
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
        self._scope_vars = []
        self._nested_vars =  {}
        self._variables_out_of_scope: Dict[str, Any] = {}
        self._all_variables_out_of_scope = []

    # TODO: Maybe set as an event?
    def _emit_warning(self, node):
        if self._all_variables_out_of_scope:
            elems = []
            for (target, _) in self._all_variables_out_of_scope:
                t_id = get_id(target)
                elems.append(f"- {t_id} on linenumber {target.lineno}")
            elems_str = "\n".join(elems)
            logger.warn(f"\033[93mWARNING { node.__file__.name}: There are variables"
                        f" used outside their scope:\n"
                        f"{elems_str}\033[0m")

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "fix_scope_bounds", False) or \
                getattr(node, "loop_scope_warning", False):
            self.generic_visit(node)
            if getattr(node, "loop_scope_warning", False):
                self._emit_warning(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._scope_analysis(node)
        return node

    def visit_If(self, node: ast.If) -> Any:
        # Visit node body
        self._scope_analysis(node)
        # Visit node orelse
        self._scope_analysis(node, attr="orelse")
        return node
    
    def visit_For(self, node: ast.For) -> Any:
        self._scope_analysis(node)
        return node
    
    def visit_While(self, node: ast.While) -> Any:
        self._scope_analysis(node)
        return node

    def visit_With(self, node: ast.With) -> Any:
        self._scope_analysis(node)
        return node

    def _scope_analysis(self, node, attr="body"):
        self._scope_vars.clear()
        self._nested_vars.clear()
        self._variables_out_of_scope = {}
        vars = set(map(get_id, node.vars))
        # Check for nested hard scopes and visit other nodes
        body = getattr(node, attr, [])
        for n in body:
            if isinstance(n, (ast.For, ast.With, ast.While, 
                    ast.If, ast.FunctionDef)):
                self._nested_vars.update({get_id(n_var): n_var 
                    for n_var in n.vars if get_id(n_var) not in vars})
            else:
                self.visit(n)
        if hasattr(node, "variables_out_of_scope"):
            node.variables_out_of_scope |= self._variables_out_of_scope
        else:
            node.variables_out_of_scope = self._variables_out_of_scope
        self._all_variables_out_of_scope.extend(self._variables_out_of_scope.values())

        # Visit remaining nodes
        for n in body:
            if isinstance(n, (ast.For, ast.With, ast.While, 
                    ast.If, ast.FunctionDef)):
                self.visit(n)

    def visit_Name(self, node: ast.Name) -> Any:
        # Check if the name is defined in any 
        # of the nested scopes
        if (id := get_id(node)) in self._nested_vars and \
                not getattr(node, "lhs", False):
            var = self._nested_vars[id]
            ann = self._get_ann(var)
            self._variables_out_of_scope[id] = (node, ann)  
        return node
    
    def _get_ann(self, node):
        if hasattr(node, "annotation"):
            return node.annotation
        if hasattr(node, "assigned_from"):
            if hasattr(node.assigned_from, "annotation"):
                return node.assigned_from.annotation
        if hasattr(node, "scopes"):
            nd = node.scopes.find(get_id(node))
            if hasattr(nd, "annotation"):
                return nd.annotation
        return None

    # The variables in List and Dictionary Comprehensions, 
    # and Lambdas should not count for the variables out of scope
    def visit_ListComp(self, node: ast.ListComp) -> Any:
        return node

    def visit_DictComp(self, node: ast.DictComp) -> Any:
        return node

    def visit_Lambda(self, node: ast.Lambda) -> Any:
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
            # If one variable is not optimizable, the others aren't either
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


class JuliaBroadcastTransformer(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._match_list = lambda x: re.match(r"^list|^List|^tuple|^Tuple", x) is not None if x else None
        self._match_matrix = lambda x: re.match(r"^Matrix|^np.ndarray", x) is not None if x else None
        self._match_scalar = lambda x: re.match(r"^int|^float|^bool", x) is not None if x else None

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        self.generic_visit(node)
        left_ann = get_ann_repr(getattr(node.left, "annotation", None))
        right_ann = get_ann_repr(getattr(node.right, "annotation", None))
        node.broadcast = (self._match_matrix(left_ann) or self._match_matrix(right_ann)) or \
            ((self._match_list(left_ann) or self._match_matrix(left_ann)) and self._match_scalar(right_ann)) or \
            ((self._match_list(right_ann) or self._match_matrix(right_ann)) and self._match_scalar(left_ann)) or \
            (getattr(node.left, "broadcast", None) and self._match_scalar(right_ann)) or \
            (getattr(node.right, "broadcast", None) and self._match_scalar(left_ann))
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        target = node.targets[0]
        ann = getattr(node.value, "annotation", None)
        ann_id = get_id(ann.value) \
            if isinstance(ann, ast.Subscript) else get_id(ann)
        # cont_type = getattr(node, "container_type", None)
        if ann_id:
            node.broadcast = isinstance(target, ast.Subscript) and \
                    isinstance(target.slice, ast.Slice) and \
                    not self._match_list(ann_id)
        return node