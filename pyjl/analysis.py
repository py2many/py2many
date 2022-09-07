
import ast
import logging
import re
from typing import Any, Dict

from py2many.ast_helpers import get_id
from py2many.helpers import get_ann_repr
from py2many.tracer import find_node_by_name_and_type
from pyjl.global_vars import FIX_SCOPE_BOUNDS, LOOP_SCOPE_WARNING

logger = logging.Logger("pyjl")


def analyse_variable_scope(node, extension=False):
    visitor = JuliaVariableScopeAnalysis()
    visitor.visit(node)


def loop_range_optimization_analysis(node, extension=False):
    visitor = JuliaLoopRangesOptimizationAnalysis()
    visitor.visit(node)


def detect_broadcast(node, extension=False):
    visitor = JuliaBroadcastTransformer()
    visitor.visit(node)

def detect_ctypes_callbacks(node, extension=False):
    visitor = DetectCtypesCallbacks()
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
        self._nested_vars =  {}
        self._variables_out_of_scope: dict[str, Any] = {}
        self._all_variables_out_of_scope = []
        self._curr_scope_vars = []
        # Two phases
        self._sweep = False
        self._filter = False

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

    def visit(self, node: ast.AST) -> Any:
        if self._sweep and hasattr(node, "vars"):
            self._sweep_phase(node)
            return node
        return super().visit(node)

    def visit_Module(self, node: ast.Module) -> Any:
        self._variables_out_of_scope = {}
        if getattr(node, FIX_SCOPE_BOUNDS, False) or \
                getattr(node, LOOP_SCOPE_WARNING, False):
            self.generic_visit(node)
            if getattr(node, LOOP_SCOPE_WARNING, False):
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
        if self._filter:
            # Get the variables from all outer scopes
            scope_vars_backup = self._curr_scope_vars
            self._curr_scope_vars = []
            for scope in node.scopes:
                if hasattr(scope, "vars"):
                    self._curr_scope_vars.extend(list(map(get_id, scope.vars)))
            self.generic_visit(node)
            # Reset state to prior scope variables
            self._curr_scope_vars = scope_vars_backup
            return node
        self._nested_vars = {}
        self._variables_out_of_scope = {}
        # Sweep phase checks for nested variables
        self._sweep = True
        self.generic_visit(node)
        self._sweep = False
        # Filter phase retrieves variables out of scope
        node.nested_variables = self._nested_vars
        self._filter = True
        self.generic_visit(node)
        self._filter = False
        # Save nested variables and variables out of scope for each node
        node.variables_out_of_scope = self._variables_out_of_scope
        self._all_variables_out_of_scope.extend(self._variables_out_of_scope.values())
        # Visit nodes in body
        body = getattr(node, attr, [])
        for n in body:
            if isinstance(n, (ast.With, ast.For, ast.While, ast.If, 
                    ast.FunctionDef, ast.Module)):
                self.visit(n)

    def _sweep_phase(self, node):
        # Perform the sweep phase (Helps detect nested variables 
        # from nested scopes)
        self.generic_visit(node)
        self._nested_vars.update({get_id(n_var): n_var 
            for n_var in node.vars})

    def visit_Name(self, node: ast.Name) -> Any:
        # Check if the name is defined in any
        # of the nested scopes
        node_id = get_id(node)
        if self._filter and \
                not getattr(node, "lhs", False) and \
                node_id in self._nested_vars:
            var = self._nested_vars[node_id]
            if node_id not in self._curr_scope_vars:
                # Guarantee that var is not in one of the 
                # parent scopes of the current node.
                ann = self._get_ann(var)
                self._variables_out_of_scope[node_id] = (node, ann)
        return node
    
    def _get_ann(self, node):
        """Attempt to get the annotation for a node"""
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


class JuliaLoopRangesOptimizationAnalysis(ast.NodeTransformer):
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
        if getattr(node, FIX_SCOPE_BOUNDS, False):
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

class DetectCtypesCallbacks(ast.NodeTransformer):
    CTYPES_CALLBACK_FACTORIES = {
        "ctypes.WINFUNCTYPE",
        "WINFUNCTYPE",
    }

    def __init__(self) -> None:
        super().__init__()

    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        ann_id = get_id(getattr(node.func, "annotation", None))
        if ann_id in {"_FuncPointer", "ctypes.FuncPointer"}:
            func_node = node.scopes.find(get_id(node.func))
            if assigned_from := getattr(func_node, "assigned_from", None):
                if isinstance(assigned_from, (ast.Assign, ast.AnnAssign)) and \
                        isinstance(assigned_from.value, ast.Call) and \
                        get_id(assigned_from.value.func) in self.CTYPES_CALLBACK_FACTORIES:
                    # Search for Julia function callable
                    callback_func = node.scopes.find(get_id(node.args[0]))
                    if isinstance(callback_func, ast.FunctionDef):
                        callback_func._is_callback = True
                        callback_func.restype = assigned_from.value.args[0]
        return node

