import ast
import copy
import ctypes
import re
from typing import Any, Dict

from py2many.clike import class_for_typename

from py2many.exceptions import AstUnsupportedOperation
from py2many.helpers import get_ann_repr
from py2many.inference import InferTypesTransformer
from py2many.scope import ScopeList
from py2many.tracer import find_closest_scope, find_node_by_name_and_type, find_node_by_type, is_class_or_module, is_class_type, is_list
from py2many.analysis import IGNORED_MODULE_SET

from py2many.ast_helpers import copy_attributes, get_id
from pyjl.clike import JL_IGNORED_MODULE_SET
from pyjl.global_vars import CHANNELS, COMMON_LOOP_VARS, FIX_SCOPE_BOUNDS, JL_CLASS, LOWER_YIELD_FROM, OBJECT_ORIENTED, OFFSET_ARRAYS, OOP_CLASS, OOP_NESTED_FUNCS, REMOVE_NESTED, REMOVE_NESTED_RESUMABLES, RESUMABLE, SEP, USE_MODULES, USE_RESUMABLES
from pyjl.helpers import generate_var_name, get_default_val, get_func_def, is_dir, is_file, obj_id
import pyjl.juliaAst as juliaAst


class JuliaMethodCallRewriter(ast.NodeTransformer):
    """Converts Python calls and attribute calls to Julia compatible ones"""
    def __init__(self) -> None:
        super().__init__()
        self._file = None
        self._basedir = None
        self._ignored_module_set = JL_IGNORED_MODULE_SET
        self._imports = []
        self._use_modules = None
        self._oop_nested_funcs = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._file = getattr(node, "__file__", ".")
        self._basedir = getattr(node, "__basedir__", None)
        self._use_modules = getattr(node, USE_MODULES, None)
        self._imports = list(map(get_id, getattr(node, "imports", [])))
        self._oop_nested_funcs = getattr(node, OOP_NESTED_FUNCS, False) 
        self.generic_visit(node)
        return node

    def visit_Call(self, node: ast.Call):
        self.generic_visit(node)

        # Special attribute used for dispatching
        node.orig_name = get_id(node.func)

        # Don't parse annotations and special nodes
        if getattr(node, "is_annotation", False) or \
                getattr(node, "no_rewrite", False) or \
                getattr(node.func, "no_rewrite", False):
            return node

        args = node.args
        fname = node.func
        if isinstance(fname, ast.Attribute):
            val_id = get_id(fname.value)
            # Bypass rewrite when using oop with nested functions
            if val_id and (is_class_type(val_id, node.scopes) or 
                    re.match(r"^self", val_id)) \
                    and self._oop_nested_funcs:
                return node
            # Check if value is module
            is_module = val_id and is_file(val_id, self._basedir)
            # Detect static class access
            class_node = node.scopes.find(val_id)
            is_static_access = is_class_or_module(val_id, node.scopes) and \
                class_node and find_node_by_name_and_type(fname.attr, 
                    ast.FunctionDef, class_node.scopes)[1]
            if (is_module and not self._use_modules) or is_static_access:
                # Handle separate module call when Julia defines no 'module'
                new_func_name = fname.attr
                node.func = ast.Name(
                    id=new_func_name, lineno=node.lineno, ctx=fname.ctx)
            elif not is_class_or_module(val_id, node.scopes):
                args = [fname.value] + args
                new_func_name = fname.attr
                node.func = ast.Name(
                    id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        node.args = args
        return node

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        self.generic_visit(node)
        # Don't parse annotations and special nodes
        if getattr(node, "is_annotation", False) or \
                getattr(node, "no_rewrite", False):
            return node
        # Get annotation
        annotation = getattr(node, "annotation", None)
        # Adds a dispatch attribute, as functions can be assigned to variables
        node.dispatch = ast.Call(
            func = ast.Name(id=node.attr, ctx=ast.Load(), lineno = node.lineno),
            args=[node.value],
            keywords=[],
            lineno=node.lineno,
            col_offset=node.col_offset,
            annotation = annotation,
            scopes = node.scopes,
            is_attr = True,
            orig_name = get_id(node), # Special attribute used for dispatching
        )
        return node


class JuliaImportNameRewriter(ast.NodeTransformer):
    "Rewrites import names when using modules"
    def __init__(self) -> None:
        super().__init__()
        self._names = {}
        self._basedir = None
    
    def visit_Module(self, node: ast.Module) -> Any:
        self._basedir = getattr(node, "__basedir__", None)
        self._names = {}
        if getattr(node, USE_MODULES, False):
            return self.generic_visit(node)
        return node
    
    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        if not node.module or not self._basedir:
            return node
        mod_name = node.module.split(".")[-1]
        is_dir_or_path = is_dir(f"{node.module}", self._basedir) or \
            is_file(f"{node.module}", self._basedir) or \
            node.level > 0 or \
            node.module == "."
        for name in node.names:
            if is_dir_or_path and \
                    not is_file(f"{node.module}.{name.name}", self._basedir) and \
                    not is_dir(f"{node.module}.{name.name}", self._basedir):
                if name.asname:
                    self._names[name.asname] = mod_name
                else:
                    self._names[name.name] = mod_name
        return node

    def visit_Name(self, node: ast.Name) -> Any:
        if node.id in self._names:
            attr_node = ast.Attribute(
                value = ast.Name(id=self._names[node.id], lineno = node.lineno),
                attr = node.id,
                ctx = ast.Load(),
                scopes = node.scopes,
                no_rewrite = True)
            ast.fix_missing_locations(attr_node)
            return attr_node
        return node
    
    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        # Rewrite module calls to calls to __init__
        func_repr = get_id(node)
        split_repr = func_repr.split(".") if func_repr else []
        if split_repr and is_dir(".".join(split_repr), self._basedir):
            self._insert_init(node)
            return node

        # Bypass imports
        for i in range(1,len(split_repr)):
            if is_dir('.'.join(split_repr[:i]), self._basedir):
                return node
        return node

    def _insert_init(self, node: ast.Attribute):
        if isinstance(node.value, ast.Attribute):
            self._insert_init(node.value)
        else:
            # Avoid referencing the same object (TODO: Is this necessary?)
            value = copy.deepcopy(node.value)
            node.value = ast.Attribute(
                value = value,
                attr = node.attr,
                ctx = ast.Load(),
                scopes = node.scopes,
                no_rewrite = True,
                lineno = node.lineno,
                col_offset = node.col_offset,
            )
            node.attr = "__init__"
            return node.value.value

class JuliaAugAssignRewriter(ast.NodeTransformer):
    """Rewrites augmented assignments into compatible 
    Julia operations"""
    def __init__(self) -> None:
        super().__init__()

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        node_target = node.target
        is_class = is_class_type(get_id(node.target), node.scopes) or \
            is_class_type(get_id(node.value), node.scopes)
        # Template for call node
        call = ast.Call(
            func = ast.Name(
                id = None,
                lineno = node.lineno,
                col_offset = node.col_offset),
            args = [],
            keywords = [],
            lineno = node.lineno,
            col_offset = node.col_offset,
            scopes = node.target.scopes)

        # New binary operation
        value = ast.BinOp(
                left=node.target,
                op=node.op,
                right=node.value,
                lineno=node.lineno,
                col_offset=node.col_offset,
                scopes = node.value.scopes)

        if isinstance(node.target, ast.Subscript) and \
                isinstance(node.target.slice, ast.Slice):
            call.func.id = "splice!"
            if self._is_number(node.value) and isinstance(node.op, ast.Mult):
                call.args.extend([node_target.value, node_target.slice, value])
                return call
            elif not self._is_number(node.value) and isinstance(node.op, ast.Add):
                lower = node_target.slice.lower
                upper = node_target.slice.upper
                if isinstance(lower, ast.Constant) and isinstance(upper, ast.Constant) and \
                        upper.value >= lower.value:
                    lower_slice = ast.Constant(value = int(upper.value) + 1, scopes = lower.scopes)
                else:
                    lower_slice = ast.Constant(value = lower.value, scopes = lower.scopes)
                new_slice = ast.Slice(
                    lower = lower_slice,
                    upper = ast.Constant(value = upper.value, scopes = upper.scopes)
                )
                call.args.extend([node_target.value, new_slice, node.value])
                return call
        elif isinstance(node.target, ast.Name) and \
                self._is_collection(node.target):
            if isinstance(node.op, ast.Add):
                call.func.id = "append!"
                call.args.append(node.target)
                call.args.append(node.value)
                return call
            elif isinstance(node.op, ast.Mult) and \
                    self._is_number(node.value):
                # append the result of repeating the value
                call.func.id = "append!"
                if isinstance(node.value, ast.Constant):
                    value = ast.Constant(value = node.value.value - 1)
                else:
                    value = ast.BinOp(
                        left = node.value,
                        op = ast.Sub(),
                        right = ast.Constant(value=1)
                    )
                ast.fix_missing_locations(value)
                repeat_arg = ast.Call(
                        func = ast.Name(id="repeat"),
                        args = [node.target, value],
                        keywords = []
                    )
                ast.fix_missing_locations(repeat_arg)
                call.args.append(node.target)
                call.args.append(repeat_arg)
                return call
            elif is_class:
                return ast.Assign(
                    targets=[node_target],
                    value = value,
                    lineno=node.lineno,
                    col_offset=node.col_offset,
                    scopes = node.scopes
                )

        return self.generic_visit(node)

    @staticmethod
    def _is_number(node):
        return isinstance(node, ast.Num) or \
                (isinstance(node, ast.Constant) and node.value.isdigit()) or \
                (get_id(getattr(node, "annotation", None)) in 
                    InferTypesTransformer.FIXED_WIDTH_INTS)

    @staticmethod
    def _is_collection(node):
        ann = getattr(node.scopes.find(get_id(node)), "annotation", None)
        if ann:
            ann_str = ast.unparse(ann)
            return re.match(r"^List|^list|^Dict|^dict|^Set|^set", ann_str) is not None
        return False


class JuliaGeneratorRewriter(ast.NodeTransformer):
    """A Rewriter for Generator functions"""
    SPECIAL_FUNCTIONS = set([
        "islice"
    ])

    def __init__(self):
        super().__init__()
        self._use_resumables = False
        self._lower_yield_from = False
        self._replace_map: Dict = {}
        self._replace_calls: Dict[str, ast.Call] = {}
        self._sweep = False

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        if (id := get_id(node)) in self._replace_map:
            return self._replace_map[id]
        return node

    def visit_Module(self, node: ast.Module) -> Any:
        # Reset state
        self._replace_calls = {}
        self._replace_map: Dict = {}
        # Get flags
        self._use_resumables = getattr(node, USE_RESUMABLES, False)
        self._lower_yield_from = getattr(node, LOWER_YIELD_FROM, False)

        self.generic_visit(node)

        # Sweep phase
        self._sweep = True
        self.generic_visit(node)
        self._sweep = False

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        if self._sweep:
            body = list(map(lambda x: self.visit(x), node.body))
            node.body = list(filter(lambda x: x is not None, body))
            return node

        body = []
        node.n_body = []
        for n in node.body:
            n_visit = self.visit(n)
            if node.n_body:
                body.extend(node.n_body)
                node.n_body = []
            if n_visit:
                body.append(n_visit)

        # Update body
        node.body = body

        ann_id = get_id(getattr(node, "annotation", None))
        if ann_id == "Generator":
            is_resumable = self._use_resumables or (RESUMABLE in node.parsed_decorators)
            is_channels = CHANNELS in node.parsed_decorators
            if is_resumable and is_channels:
                raise AstUnsupportedOperation(  
                    "Function cannot have both @resumable and @channels decorators", 
                    node)
            elif self._use_resumables and RESUMABLE not in node.parsed_decorators:
                node.parsed_decorators[RESUMABLE] = None
                node.decorator_list.append(ast.Name(id=RESUMABLE))
            elif not is_resumable and not is_channels:
                # Body contains yield and is not resumable function
                node.parsed_decorators[CHANNELS] = None
                node.decorator_list.append(ast.Name(id=CHANNELS))
        return node

    def visit_YieldFrom(self, node: ast.YieldFrom) -> Any:
        if self._sweep:
            return node
        self.generic_visit(node)
        parent = find_closest_scope(node.scopes)
        if isinstance(parent, ast.FunctionDef):
            dec = None
            if CHANNELS in parent.parsed_decorators:
                dec = parent.parsed_decorators[CHANNELS]
            elif RESUMABLE in parent.parsed_decorators:
                dec = parent.parsed_decorators[RESUMABLE]
            lower_yield_from = (dec and dec["lower_yield_from"]) or \
                self._lower_yield_from
            if lower_yield_from:
                val = ast.Name(
                        id = generate_var_name(parent, COMMON_LOOP_VARS),
                        lineno = node.lineno,
                        col_offset = node.col_offset)
                new_node = ast.For(
                    target = val,
                    iter = node.value,
                    body = [
                        ast.Yield(
                            value = val
                        )],
                    orelse = [],
                    lineno = node.lineno,
                    col_offset = node.col_offset,
                    scopes = node.scopes)
                return new_node

        return node

    def visit_With(self, node: ast.With) -> Any:
        if self._sweep:
            return node
        parent = node.scopes[-2] if len(node.scopes) >= 2 else None
        context_expr = node.items[0].context_expr
        # Bypass call to closing
        if isinstance(context_expr, ast.Call) and \
                get_id(context_expr.func) == "closing":
            context_expr = context_expr.args[0]

        opt_var = node.items[0].optional_vars
        if isinstance(context_expr, ast.Call):
            func_id = get_id(context_expr.func)
            func_def = find_node_by_name_and_type(func_id, ast.FunctionDef, node.scopes)[0]
            if func_def and RESUMABLE in func_def.parsed_decorators \
                    and parent and hasattr(parent, "body"):
                # Resumable functions cannot be called from annonymous functions
                # https://github.com/BenLauwens/ResumableFunctions.jl/blob/master/docs/src/manual.md
                prev = self._replace_map
                self._replace_map = {get_id(opt_var): context_expr}
                self.generic_visit(node)
                self._replace_map = prev
                parent.body.extend(node.body)
                return None
        return node
    
    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        if self._sweep:
            if (id := get_id(node.func)) in self._replace_calls:
                repl_call = self._replace_calls[id]
                repl_call.lineno = node.lineno
                repl_call.col_offset = node.col_offset
                repl_call.scopes = getattr(node, "scopes", ScopeList())
                return repl_call
        else:
            parent = node.scopes[-1] if len(node.scopes) >= 1 else None
            if get_id(node.func) in self.SPECIAL_FUNCTIONS and \
                    isinstance(node.args[0], ast.Call):
                args0 = node.args[0]
                args0_id = get_id(args0.func)
                func_def = get_func_def(node, args0_id)
                if func_def and RESUMABLE in func_def.parsed_decorators and \
                        parent and hasattr(parent, "n_body"):
                    resumable_name = ast.Name(id=f"{args0_id}_")
                    resumable_assign = ast.Assign(
                        targets = [resumable_name],
                        value = ast.Call(
                            func = ast.Name(id = args0_id),
                            args = [arg for arg in args0.args],
                            keywords = [arg for arg in args0.keywords],
                            # annotation = getattr(args0, "annotation", None),
                            scopes = getattr(args0, "scopes", None),
                        ),
                        scopes = getattr(args0, "scopes", None),
                        lineno = node.lineno
                    )
                    node.args[0].func = resumable_name
                    node.args[0].args = []
                    parent.n_body.append(self.visit(resumable_assign))
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        if self._sweep:
            return node

        name = get_id(node.value.value) \
            if (isinstance(node.value, ast.Attribute) and
                node.value.attr == "__next__") \
            else get_id(node.value)
        func_def = get_func_def(node, name)
        if func_def and get_id(getattr(func_def, "annotation", None)) == "Generator" and \
                RESUMABLE not in func_def.parsed_decorators:
            self._replace_calls[get_id(node.targets[0])] = ast.Call(
                func = node.value,
                args = [],
                keywords = [],
                annotation = getattr(node.value, "annotation", None)
            )
            return None
        return node


class JuliaConditionRewriter(ast.NodeTransformer):
    """Rewrites condition checks to Julia compatible ones
    All checks that perform equality checks with the literal '1'
    have to be converted to equality checks with true"""

    def __init__(self) -> None:
        super().__init__()

    def visit_If(self, node: ast.If) -> Any:
        self.generic_visit(node)
        self._generic_test_visit(node)
        return node

    def visit_While(self, node: ast.While) -> Any:
        self.generic_visit(node)
        self._generic_test_visit(node)
        return node

    def _generic_test_visit(self, node):
        # Shortcut if conditions are numbers
        if isinstance(node.test, ast.Constant):
            if node.test.value == 1 or node.test.value == "1":
                node.test.value = True
                return node
            elif node.test.value == 0:
                node.test.value = False
                return node

        annotation = getattr(node.test, "annotation", None)
        ann_id = get_id(annotation)
        if ann_id == "int" or ann_id == "float":
            node.test = self._build_compare(node.test, 
                ast.NotEq(), 0)
        
        if hasattr(node.test, "annotation"):
            type_str: str = get_ann_repr(node.test.annotation, sep=SEP)
            match = re.match(r"^Optional|^list|^List|^tuple|^Tuple", type_str) \
                if type_str else False
            if match:
                node.test = self._build_compare(node.test, 
                    ast.IsNot(), None)

    def _build_compare(self, node, op, comp_value):
        return ast.Compare(
                left = node,
                ops = [op],
                comparators = [
                    ast.Constant(
                        comp_value,
                        lineno = node.lineno,
                        col_offset = node.col_offset,
                        scopes = node.scopes)],
                lineno = node.lineno, 
                col_offset = node.col_offset,
                scopes = node.scopes)
    
    def visit_Compare(self, node: ast.Compare) -> Any:
        # Julia comparisons with 'None' use Henry Baker's EGAL predicate
        # https://stackoverflow.com/questions/38601141/what-is-the-difference-between-and-comparison-operators-in-julia
        self.generic_visit(node)
        find_none = lambda x: isinstance(x, ast.Constant) and x.value == None
        comps_none = next(filter(find_none, node.comparators), None)
        if find_none(node.left) or comps_none:
            for i in range(len(node.ops)):
                if isinstance(node.ops[i], ast.Eq):
                    node.ops[i] = ast.Is()
                elif isinstance(node.ops[i], ast.NotEq):
                    node.ops[i] = ast.IsNot()
        return node


class JuliaIndexingRewriter(ast.NodeTransformer):
    """Translates Python's 1-based indexing to Julia's 
    0-based indexing for lists"""

    SPECIAL_FUNCTIONS = set([
        "bisect",
        "bisect_right",
        "bisect_left",
        "find_ge",
        "find_gt",
        "find_le",
        "find_lt",
        "index",
    ])

    RESERVED_FUNCTIONS = set([
        "__dict__"
    ])

    def __init__(self) -> None:
        super().__init__()
        self._curr_slice_val = None
        self._valid_loop_vars = set()

    def visit_Module(self, node: ast.Module) -> Any:
        imports = getattr(node, "imports", [])
        self._imports = [get_id(a) for a in imports]
        self.generic_visit(node)
        return node

    def visit_For(self, node: ast.For) -> Any:
        targets = set()
        positive_and_ascending_range = isinstance(node.iter, ast.Call) and  \
                get_id(node.iter.func) == "range" and \
                ((len(node.iter.args) < 3 and isinstance(node.iter.args[0], ast.Constant)) or 
                (len(node.iter.args) == 3 and isinstance(node.iter.args[0], ast.Constant) and
                    isinstance(node.iter.args[2], ast.Constant)))
        if positive_and_ascending_range:
            # Iter is a call to range and has a positive start value and a 
            # positive stepping value. This implies that if there is a USub 
            # operation, that the values will be negative. The transpiler
            # can only ensure that the values are positive if they are constants.
            if isinstance(node.target, (ast.Tuple, ast.List)):
                targets = {get_id(e) for e in node.target.elts}
                self._valid_loop_vars.update(targets)
            elif isinstance(node.target, ast.Name):
                targets = {get_id(node.target)}
                self._valid_loop_vars.add(get_id(node.target))
        self.generic_visit(node)
        self._valid_loop_vars.difference_update(targets)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        # Don't rewrite nodes that are annotations
        if hasattr(node, "is_annotation"):
            return node

        self._curr_slice_val = node.value
        self.generic_visit(node)
        self._curr_slice_val = None

        # Handle negative indexing
        is_usub = lambda x: (isinstance(x, ast.UnaryOp) and 
                isinstance(x.op, ast.USub))
        end_val = ast.Name(
                id = "end",
                annotation = ast.Name(id="int"),
                preserve_keyword = True)
        if is_usub(node.slice):
            if isinstance(node.slice.operand, ast.Constant):
                if node.slice.operand.value == 1:
                    node.slice = end_val
                else:
                    node.slice = ast.BinOp(
                        left = end_val,
                        op = ast.Sub(),
                        right = ast.Constant(value = node.slice.operand.value - 1),
                        annotation = ast.Name(id = "int"),
                        lineno = node.lineno, col_offset = node.col_offset,
                        scopes = node.slice.scopes
                    )
                return node
            elif get_id(node.slice.operand) in self._valid_loop_vars:
                # Node operand is a unary operation, uses USub and is in the valid 
                # loop variables (meaning the loop is in ascending order). 
                # Therefore, the variable will have a negative value.
                node.slice = ast.BinOp(
                    left = end_val,
                    op = ast.Sub(),
                    right = node.slice.operand,
                    annotation = ast.Name(id = "int"),
                    lineno = node.lineno, col_offset = node.col_offset,
                    scopes = node.slice.scopes
                )
        elif isinstance(node.slice, ast.BinOp) and \
                isinstance(node.slice.right, ast.Constant) and \
                is_usub(node.slice.left) and \
                get_id(node.slice.left.operand) in self._valid_loop_vars:
            # Binary operation where the left node is a unary operation, 
            # uses USub and is in the valid loop variables. The variable 
            # will have a negative value. (TODO: Is this assuming too much?)
            node.slice.left = ast.BinOp(
                left = end_val,
                op = ast.Sub(),
                right = node.slice.left.operand,
                annotation = ast.Name(id = "int"),
                lineno = node.lineno, col_offset = node.col_offset,
                scopes = node.slice.scopes
            )

        # Handle non-negative indexing
        if not self._is_dict(node) and \
                not isinstance(node.slice, ast.Slice):
            call_id = None
            if isinstance(node.slice, ast.Call):
                call_id = self._get_assign_value(node.slice)

            if not getattr(node, "range_optimization", None) and \
                    not getattr(node, "using_offset_arrays", None):
                # Ignore special functions, as they already return the correct indices
                if call_id in self.SPECIAL_FUNCTIONS and \
                        call_id in self._imports:
                    return node
                if isinstance(node.value, ast.Attribute) and \
                        node.value.attr in self.RESERVED_FUNCTIONS:
                    return node

                if isinstance(node.slice, ast.Constant) \
                        and isinstance(node.slice.value, int):
                    # Shortcut if index is a numeric value
                    node.slice.value += 1
                else:
                    # Don't add 1 to string constants
                    if isinstance(node.slice, ast.Constant) and \
                            isinstance(node.slice.value, str):
                        return node

                    # Default: add 1
                    if get_id(node.slice) != "end":
                        node.slice = self._do_bin_op(node.slice, ast.Add(), 1,
                            node.lineno, node.col_offset)
            elif getattr(node, "range_optimization", None) and \
                    not getattr(node, "using_offset_arrays", None):
                # Support nested subscripts. See example at:
                # tests/cases/newman_conway_sequence.py
                if isinstance(node.scopes[-1], ast.For):
                    for_node: ast.For = node.scopes[-1]
                    target_id = get_id(for_node.target)
                    if isinstance(node.slice, ast.Subscript) or \
                            isinstance(node.slice, ast.BinOp) and \
                            not self._bin_op_contains(node.slice, target_id):
                        node.slice = self._do_bin_op(node.slice, ast.Add(), 1,
                            node.lineno, node.col_offset)
            else:
                if call_id in self.SPECIAL_FUNCTIONS and \
                        call_id in self._imports:
                    # Get corresponding assignment
                    assign_node = find_node_by_name_and_type(get_id(node.value), ast.Assign, node.scopes)[0]
                    if assign_node and isinstance(assign_node.value, ast.Call) and \
                            get_id(assign_node.value.func) == "OffsetArray":
                        dec = assign_node.value.args[1]
                        dec = -dec.value if dec.value < 0 else dec.value
                        node.slice = self._do_bin_op(node.slice, ast.Sub(), dec,
                            node.lineno, node.col_offset)

        return node

    def _bin_op_contains(self, bin_op: ast.BinOp, node_id):
        if (get_id(bin_op.left) == node_id) or \
                (get_id(bin_op.right) == node_id):
            return True
        contains = False
        if isinstance(bin_op.left, ast.BinOp):
            contains = self._bin_op_contains(bin_op.left, node_id)
        if not contains and isinstance(bin_op.right, ast.BinOp):
            contains = self._bin_op_contains(bin_op.right, node_id)
        return contains

    def _get_assign_value(self, node: ast.Call):
        """Gets the last assignment value"""
        call_id = obj_id(node.func)
        assign_node = find_node_by_name_and_type(call_id, ast.Assign, node.scopes)[0]
        if assign_node:
            if isinstance(assign_node.value, ast.Call):
                return self._get_assign_value(assign_node.value)
            elif id := obj_id(assign_node.value):
                return id 
        return call_id

    def visit_Slice(self, node: ast.Slice) -> Any:
        self.generic_visit(node)

        # Might need this later
        # elif getattr(node.lower, "splice_increment", None):
        #     # From JuliaAugAssignRewriter
        #     lower = f"({lower} + 2)"

        # Translate negative indexing
        if isinstance(node.upper,  ast.UnaryOp) \
                and isinstance(node.upper.op, ast.USub) and \
                isinstance(node.upper.operand, ast.Constant):
            node.upper = ast.BinOp(
                left = ast.Name(
                    id = "end",
                    annotation = ast.Name(id="int"),
                    preserve_keyword = True),
                op = ast.Sub(),
                right = node.upper.operand,
                lineno = node.upper.lineno,
                col_offset = node.upper.col_offset,
                scopes = node.upper.scopes)
        elif isinstance(node.lower, ast.UnaryOp) \
                and isinstance(node.lower.op, ast.USub) \
                and self._curr_slice_val:
            length = ast.Call(
                    func = ast.Name(
                        id = "length",
                        lineno = node.lineno, col_offset = node.col_offset,
                        annotation = ast.Name(id = "int")),
                    args = [self._curr_slice_val], 
                    keywords = [],
                    annotation = ast.Name(id="int"),
                    lineno = node.lineno, col_offset = node.col_offset,
                    scopes = node.lower.scopes)
            # Account for the fact that Julia indices start from 1
            if isinstance(node.lower.operand, ast.Constant) and \
                    node.lower.operand.value != 1:
                right = self._do_bin_op(node.lower.operand, ast.Add(), 1, 
                    node.lineno, node.col_offset)
                node.lower = ast.BinOp(
                    left = length,
                    op = ast.Sub(),
                    right = right,
                    lineno = node.lineno, col_offset = node.col_offset,
                    scopes = node.lower.scopes)
            else:
                node.lower = length
        elif not getattr(node, "range_optimization", None) and \
                not getattr(node, "using_offset_arrays", None):
            if isinstance(node.lower, ast.Constant) and isinstance(node.lower.value, int):
                node.lower.value += 1
            elif node.lower:
                # Default: add 1
                node.lower = self._do_bin_op(node.lower, ast.Add(), 1,
                    node.lineno, node.col_offset)

        if hasattr(node, "step"):
            # Translate reverse lookup
            if isinstance(node.step, ast.Constant) \
                    and node.step.value == -1:
                if (not node.lower and not node.upper) or \
                        (not node.upper and isinstance(node.lower, ast.Constant) \
                            and node.lower.value == -1):
                    node.lower = ast.Name(id="end", annotation = ast.Name(id = "int"))
                    node.upper = ast.Name(id="begin", annotation = ast.Name(id = "int"))
                elif not node.upper:
                    node.upper = ast.Name(id = "end", annotation = ast.Name(id = "int"))

        return node

    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        call_id = get_id(node.func)
        if (call_id == "range" or call_id == "xrange"):
            # args order: start, stop, step
            if getattr(node, "range_optimization", None) and \
                    not getattr(node, "using_offset_arrays", None):
                if len(node.args) == 1:
                    # By default, the arrays start at 1
                    node.args.append(node.args[0])
                    node.args[0] = ast.Constant(
                        value=1, 
                        scopes=getattr(node.args[0], "scopes", ScopeList()))
                elif len(node.args) > 1:
                    # increment start
                    node.args[0] = self._do_bin_op(node.args[0], ast.Add(), 1,
                        node.lineno, node.col_offset)
            else:
                # decrement stop
                if len(node.args) == 1:
                    node.args[0] = self._do_bin_op(node.args[0], ast.Sub(), 1,
                        node.lineno, node.col_offset)
                elif len(node.args) > 1:
                    node.args[1] = self._do_bin_op(node.args[1], ast.Sub(), 1,
                        node.lineno, node.col_offset)
            if len(node.args) == 3:
                # Cover reverse lookup
                if isinstance(node.args[2], ast.UnaryOp) and \
                        isinstance(node.args[2].op, ast.USub):
                    node.args[0], node.args[1] = node.args[1], node.args[0]
        return node

    def _do_bin_op(self, node, op, val, lineno, col_offset):
        left = node
        left.annotation = ast.Name(id="int")
        return ast.BinOp(
                    left = left,
                    op = op,
                    right = ast.Constant(
                        value = val, 
                        annotation = ast.Name(id= "int"),
                        scopes = node.scopes),
                    lineno = lineno,
                    col_offset = col_offset,
                    scopes = node.scopes
                )

    def _is_dict(self, node):
        ann = None
        if hasattr(node, "container_type"):
            ann = node.container_type
        elif val_annotation := getattr(node.value, 'annotation', None):
            ann = val_annotation

        # Parse ann
        if id := get_id(ann):
            ann = id
        elif isinstance(ann, tuple):
            ann = ann[0]
        return ann == "Dict" or ann == "dict"


class JuliaIORewriter(ast.NodeTransformer):
    """Rewrites IO operations into Julia compatible ones"""
    def __init__(self) -> None:
        super().__init__()

    def visit_For(self, node: ast.For) -> Any:
        self.generic_visit(node)
        if isinstance(node.iter, ast.Name):
            iter_node = node.scopes.find(get_id(node.iter))
            iter_ann = getattr(iter_node, "annotation", None)
            if get_id(iter_ann) == "BinaryIO":
                # Julia IOBuffer cannot be read by line
                node.iter = ast.Call(
                    func = ast.Name(id = "readlines"),
                    args = [ast.Name(id = get_id(node.iter))],
                    keywords = [],
                    scopes = node.iter.scopes
                )
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        # Optimization for sys.argv
        if isinstance(node.value, ast.Attribute) and \
                get_id(node.value) == "sys.argv" and \
                isinstance(node.slice, ast.Constant) and \
                node.slice.value > 0:
            node.value = ast.Name(id="ARGS")
            # Decrement value by 1, as ARGS does not include
            # module name. Optimization Rewriters will optimize
            # redundant binary operations
            node.slice = ast.BinOp(
                left = node.slice,
                op = ast.Sub(),
                right = ast.Constant(value=1)
            )
            ast.fix_missing_locations(node.slice)
            ast.fix_missing_locations(node.value)
        return node

class JuliaOrderedCollectionRewriter(ast.NodeTransformer):
    """Rewrites normal collections into ordered collections. 
    This depends on the JuliaOrderedCollectionTransformer"""
    def __init__(self) -> None:
        super().__init__()
        self._use_ordered_collections = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._use_ordered_collections = getattr(node, "use_ordered_collections", False)
        self.generic_visit(node)
        return node

    def visit_Dict(self, node: ast.Dict) -> Any:
        self.generic_visit(node)
        if getattr(node, "use_ordered_collection", None) or \
                self._use_ordered_collections:
            return juliaAst.OrderedDict(
                keys = node.keys,
                values = node.values,
                annotation = node.annotation
            )
        return node

    def visit_DictComp(self, node: ast.DictComp) -> Any:
        self.generic_visit(node)
        if getattr(node, "use_ordered_collection", None) or \
                self._use_ordered_collections:
            return juliaAst.OrderedDictComp(
                key = node.key,
                value = node.value,
                generators = node.generators,
                annotation = node.annotation
            )
        return node

    def visit_Set(self, node: ast.Set) -> Any:
        self.generic_visit(node)
        if getattr(node, "use_ordered_collection", None) or \
                self._use_ordered_collections:
            return juliaAst.OrderedSet(
                elts = node.elts,
                annotation = node.annotation
            )
        return node


class JuliaMainRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_If(self, node):
        is_main = (isinstance(node.test, ast.Compare)
                and isinstance(node.test.left, ast.Name)
                and node.test.left.id == "__name__"
                and isinstance(node.test.ops[0], ast.Eq)
                and isinstance(node.test.comparators[0], ast.Constant)
                and node.test.comparators[0].value == "__main__")
        node.is_python_main = is_main
        if is_main:
            node.python_main = is_main
            node.test.left = ast.Call(
                func = ast.Name(id="abspath", preserve_keyword=True),
                args = [ast.Name(id="PROGRAM_FILE")],
                keywords = [],
                scopes = node.test.left.scopes,
                lineno = node.test.left.lineno,
                col_offset = node.test.left.col_offset)
            node.test.comparators[0] = ast.Name(id="@__FILE__")
            ast.fix_missing_locations(node.test)
        return node

class JuliaArbitraryPrecisionRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._use_arbitrary_precision = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._use_arbitrary_precision = getattr(node, "use_arbitrary_precision", False)
        self.generic_visit(node)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        # self.generic_visit(node)
        for t in node.targets:
            self.visit(t)
        self._generic_assign_visit(node)
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        # self.generic_visit(node)
        self.visit(node.target)
        self._generic_assign_visit(node)
        return node

    def _generic_assign_visit(self, node):
        type_comment = getattr(node, "type_comment", None)
        if isinstance(node.value, ast.Constant):
            node.value = self.visit_Constant(node.value, type_comment)
        else:
            if getattr(node, "value", None):
                self.visit(node.value)

    def visit_Constant(self, node: ast.Constant, type_comment=None):
        self.generic_visit(node)
        ann = getattr(node, "annotation", None)
        if ann:
            is_int = lambda x: get_id(x) == "int"
            is_float = lambda x: get_id(x) == "float"
            func_name = "BigInt" if is_int(ann) else "BigFloat"
            if (type_comment == "BigInt" or type_comment == "BigFloat" or
                    (self._use_arbitrary_precision and 
                        (is_int(ann) or is_float(ann)))):
                lineno = getattr(node, "lineno", 0)
                col_offset = getattr(node, "col_offset", 0)
                return ast.Call(
                    func = ast.Name(id=func_name),
                    args = [ast.Constant(
                        value = node.value,
                        annotation = ann,
                        scopes = node.scopes)],
                    keywords = [],
                    lineno = lineno,
                    col_offset = col_offset,
                    annotation = ann,
                    scopes = node.scopes)
        return node


###########################################################
############### Removing nested constructs ################
###########################################################

class JuliaNestingRemoval(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._remove_nested = False
        self._remove_nested_resumables = False
        self._nested_classes = []
        self._nested_generators = []

    def visit_Module(self, node: ast.Module) -> Any:
        self._remove_nested = getattr(node, REMOVE_NESTED, False)
        self._remove_nested_resumables = getattr(node, REMOVE_NESTED_RESUMABLES, False)
        body = []
        # Add nested classes and generator functions to top scope
        for n in node.body:
            b_node = self.visit(n)
            if self._nested_generators:
                for nested in self._nested_generators:
                    nested.scopes = getattr(node, "scopes", ScopeList())
                    body.append(self.visit(nested))
                self._nested_generators = []
            if self._nested_classes:
                # Add nested classes to top scope                 
                for cls in self._nested_classes:
                    cls.scopes = getattr(node, "scopes", ScopeList())
                    body.append(self.visit(cls))
                self._nested_classes = []
            body.append(b_node)

        # Update Body
        node.body = body

        return node
    
    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        is_resumable = lambda x: RESUMABLE in x.parsed_decorators

        body = []
        for n in node.body:
            if isinstance(n, ast.FunctionDef):
                if self._remove_nested_resumables:
                    self._nested_generators.append(n)
                elif is_resumable(n):
                    resumable_dec = n.parsed_decorators[RESUMABLE]
                    if resumable_dec and \
                            REMOVE_NESTED in resumable_dec \
                            and resumable_dec[REMOVE_NESTED]:
                        self._nested_generators.append(n)
            elif isinstance(n, ast.ClassDef) and \
                    (REMOVE_NESTED in n.parsed_decorators or
                    self._remove_nested):
                self._nested_classes.append(n)
            else:
                body.append(n)
        node.body = body
        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        class_name = node.name
        body = []
        for n in node.body:
            if isinstance(n, ast.ClassDef):
                n.bases.append(ast.Name(id=f"Abstract{class_name}", ctx=ast.Load()))
                self._nested_classes.append(n)
            else:
                body.append(self.visit(n))
        # Update body
        node.body = body
        return node


class JuliaImportRewriter(ast.NodeTransformer):
    """Rewrites nested imports to the module scope"""
    def __init__(self) -> None:
        super().__init__()
        # The default module represents all Import nodes.
        # ImportFrom nodes have the module as key.
        self._import_names: Dict[str, list[str]] = {}
        self._nested_imports = []
        self._import_cnt = 0

    def visit_Module(self, node: ast.Module) -> Any:
        self._import_names = {}
        self._nested_imports = []
        self._import_cnt = 0
        self.generic_visit(node)
        node.body = self._nested_imports + node.body
        node.import_cnt = self._import_cnt
        # Update imports
        for imp in self._nested_imports:
            for name in imp.names:
                if name not in node.imports:
                    node.imports.append(name)
        return node

    def visit_If(self, node: ast.If) -> Any:
        return self._generic_import_scope_visit(node)

    def visit_With(self, node: ast.With) -> Any:
        return self._generic_import_scope_visit(node)

    def _generic_import_scope_visit(self, node):
        if hasattr(node, "imports"):
            del node.imports
        self.generic_visit(node)
        return node
    
    def visit_Import(self, node: ast.Import) -> Any:
        return self._generic_import_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        return self._generic_import_visit(node, node.module)

    def _generic_import_visit(self, node, key = "default"):
        self._import_cnt += 1
        if key not in self._import_names:
            self._import_names[key] = []
        aliases = []
        for alias in node.names:
            name = alias.name
            if name not in self._import_names[key]:
                self._import_names[key].append(name)
                aliases.append(alias)
        if not aliases:
            return None
        node.names = aliases
        # self.generic_visit(node)
        parent = node.scopes[-1] if len(node.scopes) >= 1 else None
        if parent and not isinstance(parent, ast.Module):
            self._nested_imports.append(node)
            return None
        return node


###########################################################
##################### Class Rewriters #####################
###########################################################

class JuliaClassWrapper(ast.NodeTransformer):
    # A hack to support two alternatives of translating 
    # Python classes to Julia
    def __init__(self) -> None:
        super().__init__()
        self._has_dict = False
        self._has_getfield = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._has_dict = False
        self._has_getfield = False
        if hasattr(node, OBJECT_ORIENTED):
            visitor = JuliaClassOOPRewriter()
        else:
            visitor = JuliaClassSubtypingRewriter()
        node = visitor.visit(node)
        body = []
        for n in node.body:
            body.append(self.visit(n))
            if isinstance(n, ast.ClassDef) and self._has_dict \
                    and not self._has_getfield:
                body.append(self._build_get_property_func(n, node.scopes))
                self._has_dict = False
                self._has_getfield = False
        node.body = body
        return node

    def _build_get_property_func(self, class_node: ast.ClassDef, scopes):
        get_property_func = ast.FunctionDef(
            name = "Base.getproperty", # Hack to set the correct name
            args = ast.arguments(
                args = [
                    ast.arg(arg = "self", annotation = ast.Name(id=class_node.name)),
                    ast.arg(arg = "property", annotation = ast.Name(id="Symbol"))],
                defaults = []
            ),
            body = [
                    ast.Assign(
                        targets = [ast.Name(id="__dict__")],
                        value = ast.Call(
                            func = ast.Attribute(
                                value = ast.Name("Base"), 
                                attr = "getattribute", 
                                ctx = ast.Load(),
                                scopes = scopes),
                            args=[ast.Name(id="self"), juliaAst.Symbol(id="__init__")],
                            keywords = [],
                            no_rewrite=True,
                            scopes = scopes
                        ),
                        scopes = scopes,
                    ),
                    ast.If(
                        test = ast.Call(
                            func=ast.Name(id="haskey"), 
                            args = [ast.Name(id="__init__"), ast.Name(id="property")],
                            keywords = [],
                            no_rewrite=True,
                            scopes = scopes),
                        body = [
                            ast.Return(value = 
                                ast.Subscript(
                                    value=ast.Name(id="__dict__"), 
                                    slice=ast.Name(id="property"))
                            )],
                        orelse = []
                    ),
                    ast.Return(value = 
                        ast.Call(
                            func = ast.Attribute(
                                value = ast.Name("Base"), 
                                attr = "getfield", 
                                ctx = ast.Load(),
                                scopes = scopes),
                            args=[ast.Name(id="self"), ast.Name(id="property")],
                            keywords = [],
                            no_rewrite=True,
                            scopes = scopes)
                    ),
                ],
            decorator_list = [],
            scopes = scopes,
            parsed_decorators = {},
        )
        ast.fix_missing_locations(get_property_func)
        return get_property_func

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self.generic_visit(node)
        ann = ast.Subscript(
            value = ast.Name(id="Dict"),
            slice = ast.Tuple(
                elts=[ast.Name(id="Symbol"), ast.Name(id="Any")],
                is_annotation = True),
            is_annotation = True,
        )
        if self._has_dict:
            body = []
            assign = ast.AnnAssign(
                target=ast.Attribute(
                    value = ast.Name(id="self"),
                    attr = "__dict__", 
                    ctx = ast.Load(),
                    scopes = node.scopes),
                value = ast.Dict(keys=[], values=[], annotation=ann),
                annotation = ann
                )
            if isinstance(node.body[0], ast.FunctionDef):
                if node.body[0].name != "__init__":
                    # Build a dunder init to get arround new __dict__ arg
                    init_func = ast.FunctionDef(
                        name="__init__", args = ast.arguments(args=[], defaults=[]), body = [assign], 
                        decorator_list = [], parsed_decorators = {})
                    ast.fix_missing_locations(init_func)
                    body.append(init_func)
                else:
                    ast.fix_missing_locations(assign)
                    node.body[0].body.append(assign)
            node.body = body + node.body
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self.generic_visit(node)
        if node.name == "__getattr__":
            self._has_getfield = True
        return node

    def visit_Call(self, node: ast.Call) -> Any:
        func_id = ast.unparse(node.func)
        if re.match(r"^super", func_id) is not None:
            # Matches any call starting with super
            # According to C3 MRO, a call to super() will select 
            # the first base class
            class_node = find_node_by_type(ast.ClassDef, node.scopes)
            base = class_node.bases[0] if class_node else None
            node.func = base
        elif isinstance(node.func, ast.Attribute) and \
                re.match(r"^.*__init__$", func_id):
            # Matches any call that ends with init
            node.func = node.func.value
        # Remove self
        if node.args and isinstance(node.args[0], ast.Name) and \
                get_id(node.args[0]) == "self":
            node.args = node.args[1:]
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        target = node.targets[0]
        # Detect if objects are being added as fields
        if isinstance(target, ast.Subscript) and \
                get_id(target.value) == "self.__dict__":
            self._has_dict = True
        elif get_id(target) == "self.__dict__":
            self._has_dict = True
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self.generic_visit(node)
        if isinstance(node.value, ast.Attribute) and \
                node.value.attr == "__dict__":
            # Wrap __dict__ values into Julia Symbols
            node.slice = ast.Call(
                func=ast.Name(id="Symbol"),
                args = [node.slice], 
                keywords=[],
                scopes = getattr(node, "scopes", None))
            ast.fix_missing_locations(node.slice)
        return node

class JuliaClassOOPRewriter(ast.NodeTransformer):
    """Adds decorators to OOP classes and differentiate 
    functions within OOP classes"""
    def __init__(self) -> None:
        super().__init__()
        self._is_oop = False
        self._oop_nested_funcs = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._oop_nested_funcs = getattr(node, OOP_NESTED_FUNCS, False)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self.generic_visit(node)
        if self._is_oop:
            node.oop = True
            node.oop_nested_func = self._oop_nested_funcs
        return node
    
    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        # Add OO decorator
        decorator = ast.Call(
            func=ast.Name(id=OOP_CLASS), 
            args=[], 
            keywords=[])
        keywords = None
        if self._oop_nested_funcs:
            decorator.keywords.append(ast.keyword(
                arg = "oop_nested_funcs", 
                value = ast.Constant(value=True)))
            keywords = {"oop_nested_funcs": True}
        node.decorator_list.append(decorator)
        node.parsed_decorators["oop_class"] = keywords
        node.jl_bases = node.bases
        # Visit OOP class
        self._is_oop = True
        for n in node.body:
            if isinstance(n, ast.ClassDef):
                n.is_nested = True
            self.visit(n)
        if not getattr(node, "is_nested", False):
            self._is_oop = False
        return node

class JuliaClassSubtypingRewriter(ast.NodeTransformer):
    """Simple Rewriter that transforms Python classes using Julia's subtyping"""

    IGNORE_EXTENDS_SET = set([
        "IntEnum",
        "IntFlag",
        "Enum",
        "Object",
    ])

    def __init__(self) -> None:
        super().__init__()
        self._ignored_module_set = \
            self._ignored_module_set = IGNORED_MODULE_SET.copy()\
                .union(JL_IGNORED_MODULE_SET.copy())
        self._hierarchy_map = {}
        self._class_scopes = []

    def visit_Module(self, node: ast.Module) -> Any:
        self._hierarchy_map = {}
        self._class_scopes = []
        node.lineno = 0
        node.col_offset = 0

        self.generic_visit(node)

        # Visit body nodes
        body = node.body

        # Create abstract types
        abstract_types = []
        l_no = node.import_cnt
        for class_name, extends in self._hierarchy_map.items():
            nameVal = ast.Name(id=class_name)
            extends = None
            core_module = extends.split(
                ".")[0] if extends else None
            if extends and core_module not in self._ignored_module_set:
                extends_name = f"Abstract{extends}" \
                    if extends in self._hierarchy_map \
                    else extends
                extends = ast.Name(id=f"{extends_name}")
            abstract_types.append(juliaAst.AbstractType(value=nameVal, extends = extends,
                                    ctx=ast.Load(), lineno=l_no, col_offset=0))
            # increment linenumber
            l_no += 1

        if abstract_types:
            body = body[:node.import_cnt] + \
                abstract_types + body[node.import_cnt:]

        node.body = body

        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self.generic_visit(node)

        # Certain classes do not need a hierarchy
        base_ids = set(map(get_id, node.bases))
        if base_ids.intersection(self.IGNORE_EXTENDS_SET):
            return node

        class_name: str = get_id(node)

        decorator_list = list(map(get_id, node.decorator_list))
        if JL_CLASS in decorator_list:
            node.jl_bases = node.bases
            return node

        extends = None
        # Change bases to support Abstract Types
        node.jl_bases = [
            ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]
        if len(node.bases) == 1:
            name = get_id(node.bases[0])
            extends = name
        elif len(node.bases) > 1:
            raise Exception("Multiple inheritance is only supported with ObjectOriented.jl")

        self._hierarchy_map[class_name] = extends

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self.generic_visit(node)

        args = node.args
        for arg in args.args:
            if ((annotation := getattr(arg, "annotation", None)) and
                    is_class_or_module(annotation, node.scopes)):
                setattr(annotation, "id", f"Abstract{annotation}")

        if (hasattr(node, "self_type") and
                is_class_or_module(node.self_type, node.scopes)):
            node.self_type = f"Abstract{node.self_type}"

        return node


###########################################################
################## Conditional Rewriters ##################
###########################################################

class VariableScopeRewriter(ast.NodeTransformer):
    """Rewrites variables in case they are defined withing one 
    of Julia's local hard/soft scopes but used outside of their scopes. 
    This has to be executed after the JuliaVariableScopeAnalysis transformer """
    def __init__(self) -> None:
        super().__init__()
        self._variables_out_of_scope = None
        self._target_vals: list[tuple] = []
    
    def visit_Module(self, node: ast.Module) -> Any:
        self._variables_out_of_scope = None
        self._target_vals = []
        if getattr(node, FIX_SCOPE_BOUNDS, False):
            self._generic_scope_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_visit(node)
        return node
    
    def _generic_scope_visit(self, node):
        body = []
        # Cover nested scopes
        target_state = self._variables_out_of_scope
        self._variables_out_of_scope = getattr(node, "variables_out_of_scope", {})
        for n in node.body:
            self.visit(n)
            if self._target_vals:
                for target, default in self._target_vals:
                    assign = ast.Assign(
                        targets=[target],
                        value = default,
                        # annotation = ast.Name(id= "int"),
                        lineno = node.lineno - 1,
                        col_offset = node.col_offset,
                        scopes = n.scopes)
                    body.append(assign)
                self._target_vals = []

            body.append(n)
            
        # Update node body
        node.body = body
        self._variables_out_of_scope = target_state
        
        return node
    
    def visit_For(self, node: ast.For) -> Any:
        target_id = get_id(node.target)
        if target_id in self._variables_out_of_scope:
            annotation = getattr(node.scopes.find(target_id), "annotation", None)
            target = ast.Name(
                        id = target_id,
                        annotation = annotation)
            
            new_loop_id = f"_{target_id}"
            new_var_assign = ast.Assign(
                targets=[target],
                value = ast.Name(
                    id = new_loop_id,
                    annotation = annotation),
                # annotation = annotation,
                lineno = node.lineno + 1,
                col_offset = node.col_offset,
                scopes = node.scopes)
            node.target.id = new_loop_id
            ast.fix_missing_locations(new_var_assign)
            node.body.insert(0, new_var_assign)
            # We provide int as an annotation, as we are 
            # dealing with a for loop with a call to range 
            # (currently the only for loops optimizable)
            self._add_target_val(node, target_id, 
                getattr(node.iter, "annotation", None))
        self.generic_visit(node)
        return node

    def visit_Name(self, node: ast.Name) -> Any:
        id = get_id(node)
        self._add_target_val(node, id)
        return node

    def _add_target_val(self, node, id, opt_ann=None):
        if id in self._variables_out_of_scope:
            # Get variable and its default value
            _, ann = self._variables_out_of_scope[id]
            target_default = get_default_val(node, opt_ann) \
                if opt_ann else get_default_val(node, ann)
            target_val = ast.Name(id=id)
            ast.fix_missing_locations(target_val)
            self._target_vals.append((target_val, target_default))
            self._variables_out_of_scope.pop(id)


class JuliaOffsetArrayRewriter(ast.NodeTransformer):
    """Converts array calls to OffsetArray calls. It is still
    a preliminary feature"""

    SUPPORTED_OPERATIONS = set([
        "append", 
        "clear",
        "extend",
        "len",
        "range"
    ])

    def __init__(self) -> None:
        super().__init__()
        # Scoping information
        self._list_assigns = []
        self._subscript_vals = []
        self._list_assign_idxs: list[int] = []
        self._subscript_val_idxs: list[int] = []
        self._last_scopes: list[ScopeList] = []
        self._current_scope = ScopeList()
        # Flags
        self._use_offset_array = False
        self._using_offset_arrays = False
        self._is_assign_val = False

    ##########################################
    ############## Visit Scopes ##############
    ##########################################

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "offset_arrays", False):
            self._using_offset_arrays = True
        self._enter_scope(node)
        self.generic_visit(node)
        self._leave_scope(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        parsed_decorators: Dict[str, Dict[str, str]] = node.parsed_decorators
        if not ((OFFSET_ARRAYS in parsed_decorators) or self._using_offset_arrays):
            return node

        self._enter_scope(node)

        # Visit body 
        return_node: ast.Return = None
        self._use_offset_array = True

        body_range = None
        if isinstance(node.body[-1], ast.Return):
            return_node = node.body[-1]
            body_range = node.body[:-1]
        else:
            body_range = node.body

        body = []
        func_assingments = []
        for n in body_range:
            self.visit(n)
            if return_node:
                if isinstance(n, ast.Assign):
                    target_ids = [get_id(t) for t in n.targets]
                    if get_id(return_node.value) in target_ids:
                        func_assingments.append(n)
                        continue
                elif isinstance(n, ast.AnnAssign):
                    if get_id(n.target) == get_id(return_node.value):
                        func_assingments.append(n)
                        continue
            body.append(n)

        if return_node:
            self.visit(return_node)

        self._use_offset_array = False

        # Visit args
        let_assignments = []
        for arg in node.args.args:
            arg_id = arg.arg
            annotation_id = get_ann_repr(arg.annotation, sep=SEP)
            is_list = re.match(r"^List|^list", annotation_id)
            if not hasattr(arg, "annotation") or \
                    (hasattr(arg, "annotation") and not is_list) or \
                    arg_id not in self._subscript_vals:
                continue
            arg_name = ast.Name(id=arg_id)
            val = self._build_offset_array_call(
                        arg_name, arg.annotation, node.lineno, 
                        node.col_offset, node.scopes)
            assign = ast.Assign(
                    targets = [arg_name],
                    value = val,
                    annotation = arg.annotation, 
                    lineno = node.lineno + 1,
                    col_offset = node.col_offset,
                    scopes = node.scopes # TODO: Remove the return statement form scopes
                )
            ast.fix_missing_locations(assign)
            let_assignments.append(assign)
        
        # Construct new body
        if let_assignments:
            let_stmt = juliaAst.LetStmt(
                    args = let_assignments,
                    body = body,
                    ctx = ast.Load(),
                    lineno = node.lineno + 1,
                    col_offset = node.col_offset
                )
            node.body = []
            if func_assingments:
                node.body.extend(func_assingments)
            node.body.append(let_stmt)
            if return_node:
                node.body.append(return_node)

        # Add to decorators
        if not (OFFSET_ARRAYS in parsed_decorators) and (let_assignments or self._list_assigns):
            node.decorator_list.append(ast.Name(id="offset_arrays"))
            parsed_decorators["offset_arrays"] = {}

        self._leave_scope(node)

        return node

    def visit_For(self, node: ast.For) -> Any:
        self._last_scopes.append(self._current_scope.copy())
        self._current_scope = node.scopes
        self.generic_visit(node)
        if self._use_offset_array:
            node.iter.using_offset_arrays = True
            node.iter.require_parent = False
        self._current_scope = ScopeList(self._last_scopes.pop())
        return node

    def visit_With(self, node: ast.With) -> Any:
        self._last_scopes.append(self._current_scope.copy())
        self._current_scope = node.scopes
        self.generic_visit(node)
        self._current_scope = ScopeList(self._last_scopes.pop())
        return node

    def visit_If(self, node: ast.If) -> Any:
        self._last_scopes.append(self._current_scope.copy())
        self._current_scope = node.scopes
        self.generic_visit(node)
        self._current_scope = ScopeList(self._last_scopes.pop())
        return node

    def _enter_scope(self, node):
        self._list_assign_idxs.append(len(self._list_assigns))
        self._subscript_val_idxs.append(len(self._subscript_vals))
        self._last_scopes.append(self._current_scope.copy())
        self._current_scope = node.scopes

    def _leave_scope(self, node):
        del self._list_assigns[self._list_assign_idxs.pop():]
        del self._subscript_vals[self._subscript_val_idxs.pop():]
        self._current_scope = ScopeList(self._last_scopes.pop())

    ##########################################
    ##########################################
    ##########################################

    def visit_List(self, node: ast.List) -> Any:
        self.generic_visit(node)
        if self._use_offset_array:
            if self._is_assign_val:
                return self._build_offset_array_call(
                    node, node.annotation,  node.lineno, 
                    node.col_offset, node.scopes)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        for t in node.targets:
            t.require_parent = False
        ann = getattr(node.value, "annotation", None)
        if self._use_offset_array and is_list(node.value):
            for n in node.targets:
                if id := get_id(n):
                    self._list_assigns.append(id)
            node.value = self._build_offset_array_call(
                node.value, ann, node.lineno, 
                node.col_offset, node.scopes)
            self.generic_visit(node)
        else:
            self._is_assign_val = True
            self.generic_visit(node)
            self._is_assign_val = False
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        node.target.require_parent = False
        if self._use_offset_array and is_list(node.value):
            # node.annotation = ast.Name(id="OffsetArray")
            self._list_assigns.append(get_id(node.target))
            node.value = self._build_offset_array_call(
                node.value, node.annotation, node.lineno, 
                node.col_offset, node.scopes)
            self.generic_visit(node)
        else:
            self._is_assign_val = True
            self.generic_visit(node)
            self._is_assign_val = False
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        node.value.require_parent = False
        self.generic_visit(node)

        # Cover nested subscripts
        if isinstance(node.value, ast.Subscript):
            node.using_offset_arrays = getattr(node.value, "using_offset_arrays", False)

        container_type = getattr(node, "container_type", None)
        is_list = container_type and re.match(r"^list|List", container_type[0])
        if self._use_offset_array and (id := get_id(node.value)) and \
                is_list:
            self._subscript_vals.append(id)
            node.using_offset_arrays = True
            if isinstance(node.slice, ast.Slice):
                node.slice.using_offset_arrays = True

        return node

    def visit_Call(self, node: ast.Call) -> Any:
        # Accounts for JuliaMethodCallRewriter
        args = getattr(node, "args", None)
        if (args and get_id(args[0]) == "sys" 
                and get_id(node.func) == "argv"):
            curr_val = self._use_offset_array
            self._use_offset_array = False
            self.generic_visit(node)
            self._use_offset_array = curr_val
            return node
        if get_id(node.func) in self.SUPPORTED_OPERATIONS:
            for arg in node.args:
                arg.require_parent = False

        self.generic_visit(node)
        return node

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        require_parent = getattr(node, "require_parent", True)
        if require_parent and get_id(node) in self._list_assigns:
            return self._create_parent(node, node.lineno, 
                getattr(node, "col_offset", None))
        return node

    def _build_offset_array_call(self, list_arg, annotation, lineno, col_offset, scopes):
        return ast.Call(
            func = ast.Name(id="OffsetArray", lineno=lineno, col_offset=col_offset),
            args = [list_arg, ast.Constant(value=-1, scopes=scopes)],
            keywords = [],
            annotation = annotation,
            lineno = lineno,
            col_offset = col_offset, 
            scopes = scopes)

    def _create_parent(self, node, lineno, col_offset):
        # TODO: Unreliable annotations when calling parent
        arg_id = get_id(node)
        new_annotation = getattr(self._current_scope.find(arg_id), "annotation", None)
        return ast.Call(
            func=ast.Name(id = "parent", lineno = lineno, col_offset = col_offset),
            args = [node],
            keywords = [],
            annotation = new_annotation,
            lineno = lineno,
            col_offset = col_offset if col_offset else 0,
            scopes = self._current_scope)


class JuliaModuleRewriter(ast.NodeTransformer):
    """Wraps Python's modules into Julia Modules."""
    def __init__(self) -> None:
        super().__init__()

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, USE_MODULES, None):
            name = node.__file__.name.split(".")[0]
            julia_module = juliaAst.JuliaModule(
                body = node.body,
                name = ast.Name(id = name),
                context = ast.Load(),
                scopes = node.scopes,
                lineno = 0,
                col_offset = 0,
                vars = getattr(node, "vars", None),
                __basedir__ = getattr(node, "__basedir__", None)
            )
            ast.fix_missing_locations(julia_module)

            # Populate remaining fields
            copy_attributes(node, julia_module)

            return julia_module
        return node


###########################################################
######################### ctypes ##########################
###########################################################

class JuliaCTypesRewriter(ast.NodeTransformer):
    """Translate ctypes to Julia. Must run before JuliaClassWrapper and 
    JuliaMethodCallRewriter"""

    CTYPES_CONVERSION_MAP = {
        "int": "ctypes.c_int",
        "float": "ctypes.c_float",
        "bool": "ctypes.c_bool",
    }
    # The idea is to keep the ctypes module in pyjl/external/modules isolated
    # from any rewriters
    CTYPES_LIST = [
        ctypes.c_int, ctypes.c_int8, ctypes.c_int16, ctypes.c_int32,
        ctypes.c_int64, ctypes.c_uint8, ctypes.c_uint16, ctypes.c_uint32,
        ctypes.c_uint64, ctypes.c_bool, ctypes.c_float, ctypes.c_double,
        ctypes.c_short, ctypes.c_ushort, ctypes.c_long, ctypes.c_ulong,
        ctypes.c_longlong, ctypes.c_ulonglong, ctypes.c_longdouble,
        ctypes.c_byte, ctypes.c_ubyte, ctypes.c_char, ctypes.c_size_t,
        ctypes.c_ssize_t, ctypes.c_char_p, ctypes.c_wchar_p, ctypes.c_void_p,
    ]

    def __init__(self) -> None:
        super().__init__()
        # Mapped as: {module_name: {named_func: {argtypes: [], restype: <return_type>}}
        # or as {func_name:{argtypes: [], restype: <return_type>}} for NamedFuncPointer
        self._ext_modules = {}
        self._imported_names = {}
    
    def visit_Module(self, node: ast.Module) -> Any:
        self._imported_names = getattr(node, "imported_names", None)
        self._use_modules = getattr(node, USE_MODULES, False)
        self.generic_visit(node)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        target = node.targets[0]
        return self._ctypes_assign_visit(node, target)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        return self._ctypes_assign_visit(node, node.target)

    def _ctypes_assign_visit(self, node, target) -> Any:
        self.generic_visit(node)
        # Check if the target is what we are looking for
        admissible_args = re.match(r".*argtypes$|.*restype$|.*errcheck$", get_id(target)) \
            if get_id(target) else False
        t_node = None
        if isinstance(target, ast.Attribute):
            attr_lst = get_id(target).split(".")
            if attr_lst[0] == "self":
                class_node = find_node_by_type(ast.ClassDef, node.scopes)
                t_node = class_node.scopes.find(attr_lst[1])
            else:
                t_node = node.scopes.find(attr_lst[0])
        else:
            t_node = target
        annotation = getattr(t_node, "annotation", None)
        if not annotation or \
                not admissible_args:
            return node

        if get_id(annotation) == ("ctypes.CDLL" or "CDLL" or 
                    "ctypes.WinDLL" or "WinDLL") and \
                isinstance(target, ast.Attribute) and \
                isinstance(target.value, ast.Attribute):
            # Adding information about modules and named functions
            module_name = None
            if isinstance(target.value.value, ast.Attribute) and \
                    get_id(target.value.value.value) == "self":
                module_name = target.value.value.attr
            elif isinstance(target.value.value, ast.Name):
                module_name = get_id(target.value.value)
            else:
                return node
            named_func = target.value.attr
            attr = target.attr

            if module_name not in self._ext_modules:
                self._ext_modules[module_name] = {named_func: {attr: node.value}}
            else:
                if named_func not in self._ext_modules[module_name]:
                    self._ext_modules[module_name][named_func] = {attr: node.value}
                else:
                    if attr not in self._ext_modules[module_name][named_func]:
                        self._ext_modules[module_name][named_func][attr] = node.value
        elif get_id(annotation) == ("ctypes._NamedFuncPointer" or "_NamedFuncPointer"):
            func_str = None
            func_ptr_var = get_id(target).split(".")
            if func_ptr_var[0] == ("self"):
                func_str = func_ptr_var[1]
            else:
                func_str = func_ptr_var[0]
            attr = func_ptr_var[-1]
            if func_str not in self._ext_modules:
                self._ext_modules[func_str] = {attr: node.value}
            else:
                if attr not in self._ext_modules[func_str]:
                    self._ext_modules[func_str][attr] = node.value
        else:
            return node

        # We want to discard such nodes, as they are not used in Julia
        return None

    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        func = node.func
        # Handle module calls
        if isinstance(node.func, ast.Attribute) and \
                get_id(node.func).split(".")[0] in self._imported_names:
            if isinstance(node.func.value, ast.Attribute):
                func.value = node.func.value.value
            else:
                func = ast.Name(id=node.func.attr)

        # Ignore calls that Load the library
        if class_for_typename(get_id(func), None, self._imported_names) \
                is ctypes.cdll.LoadLibrary:
            return node

        # Prepare args
        args = {}
        ccall_func = None
        if isinstance(func, ast.Attribute):
            # Check if call is to a dll
            module_name = None
            if isinstance(func.value, ast.Name):
                dll_node = node.scopes.find(get_id(func.value))
                module_name = get_id(func.value)
            elif isinstance(func.value, ast.Attribute) and \
                    get_id(func.value.value) == "self":
                class_node = find_node_by_type(ast.ClassDef, node.scopes)
                dll_node = class_node.scopes.find(func.value.attr)
                module_name = func.value.attr
            else:
                return node
            if get_id(getattr(dll_node, "annotation", None)) == ("ctypes.CDLL" or "CDLL"):
                # Attempt to use the stored information
                named_func = func.attr
                if module_name in self._ext_modules and \
                        named_func in self._ext_modules[module_name]:
                    args = self._ext_modules[module_name][named_func]
                    (argtypes, restype, errcheck) = self._parse_args(node, args)
                    # Insert call to Libdl.dlsym
                ccall_func = ast.Call(
                    func = ast.Attribute(
                        value = ast.Name(id = "Libdl"),
                        attr = "dlsym",
                        ctx = ast.Load(),
                        scopes = node.scopes),
                    args = [ast.Name(id=module_name), juliaAst.Symbol(id=named_func)],
                    keywords = [])
        elif get_id(getattr(node.scopes.find(get_id(func)), "annotation", None)) == \
                ("ctypes._NamedFuncPointer" or "_NamedFuncPointer"):
            # Using node.func to consider the original name
            func_id = get_id(node.func).removeprefix("self") # remove self, if any
            args = self._ext_modules[func_id] \
                if func_id in self._ext_modules else {}
            ccall_func = node.func

        (argtypes, restype, errcheck) = self._parse_args(node, args)
        if argtypes and restype and ccall_func:
            # Fill in remaining fields
            # lineno and col_offset added for debugging
            if not hasattr(ccall_func, "lineno"):
                ccall_func.lineno = node.lineno 
            if not hasattr(ccall_func, "col_offset"):
                ccall_func.col_offset = node.col_offset
            ccall_func.no_rewrite = True # Special attribute not to rewite call
            ccall_func.scopes = node.scopes
            ast.fix_missing_locations(ccall_func)
            # Add ccall
            ccall =  ast.Call(
                func = ast.Name(id="ccall"),
                args = [ccall_func, restype, argtypes],
                keywords = [],
                lineno = node.lineno + 1,
                col_offset = node.col_offset,
                scopes = node.scopes)
            ccall.args.extend(node.args)
            ccall.keywords = node.keywords
            ccall.no_rewrite = True # Special attribute not to rewite call
            return ccall
        return node

    def _parse_args(self, node, args):
        argtypes = None
        restype = None
        errcheck = None
        # Attempt to get ccall fields
        if "argtypes" in args:
            t_argtypes = args["argtypes"]
            # Elements are all annotations
            if isinstance(t_argtypes, ast.List):
                argtypes = ast.Tuple(elts = t_argtypes.elts)
            else:
                argtypes = t_argtypes
        if "restype" in args:
            restype = args["restype"]
        # Assign defaults if necessary
        if not argtypes:
            # Try to get the types from type casts or from 
            # type annotations
            argtypes_lst = []
            for arg in node.args:
                if getattr(arg, "annotation", None):
                    if (id := get_id(arg.annotation)) in self.CTYPES_CONVERSION_MAP:
                        converted_type = self.CTYPES_CONVERSION_MAP[id]
                        argtypes_lst.append(ast.Name(id=converted_type, 
                            lineno=node.lineno, col_offset=node.col_offset))
                    else:
                        argtypes_lst.append(arg.annotation)
                elif isinstance(arg, ast.Call) and \
                        class_for_typename(get_id(arg.func), None, 
                            self._imported_names) in self.CTYPES_LIST:
                    argtypes_lst.append(arg.func)
                elif isinstance(arg, ast.Call) and \
                        get_id(arg.func) == "ctypes.cast":
                    argtypes_lst.append(arg.args[1])
                else:
                    argtypes_lst.append(ast.Subscript(
                        value = ast.Name(id="Ptr"),
                        slice=ast.Name(id="Cvoid"),
                        lineno=node.lineno,
                        col_offset=node.col_offset))

            argtypes = ast.Tuple(elts = argtypes_lst)
            
        if not restype:
            restype = ast.Name(id="Cvoid")

        for arg in argtypes.elts:
            arg.is_annotation = True
        restype.is_annotation = True
        
        ast.fix_missing_locations(restype)
        ast.fix_missing_locations(argtypes)

        return (argtypes, restype, errcheck)


class JuliaArgumentParserRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        # Maps {arg_settings_inst: {
        #       "-arg_name"
        #           arg_type = Int
        #           default = 0
        #       ...
        #   }
        self._args = {}

    def visit_Module(self, node: ast.Module) -> Any:
        self._args = {}
        body = []
        for n in node.body:
            n = self.visit(n)
            if n:
                body.append(n)
        for (arg_settings_inst, (lineno, arg_vals)) in self._args.items():
            arg_node = juliaAst.Block(
                name = arg_settings_inst,
                body = arg_vals,
                vars = [],
                decorator_list = [ast.Name(id = "add_arg_table", ctx=ast.Load())],
                scopes = ScopeList(),
            )
            ast.fix_missing_locations(arg_node)
            idx = 0
            for i in range(len(node.body)):
                n = node.body[i]
                if n.lineno > lineno:
                    idx = i
                    break
            # Insert is innefficient. However, there should only be one call
            # to ArgumentParser
            body.insert(idx, arg_node)
        node.body = body
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        if isinstance(node.value, ast.Call) and \
                get_id(node.value.func) == "argparse.ArgumentParser":
            # Avoid visiting the call that sets up the ArgumentParser instance
            self._args[get_id(node.targets[0])] = (node.lineno, [])
        else:
            node = self.generic_visit(node)
        return node

    def visit_Expr(self, node: ast.Expr) -> Any:
        node = self.generic_visit(node)
        if not hasattr(node, "value"):
            return None 
        if node.value == None:
            return None
        return node

    def visit_Call(self, node: ast.Call) -> Any:
        if isinstance(node.func, ast.Attribute) and \
                isinstance(node.func.value, ast.Name) and \
                node.func.attr == "add_argument":
            arg_settings_inst = get_id(node.func.value)
            argparse_node = node.scopes.find(arg_settings_inst)
            if get_id(getattr(argparse_node, "annotation", None)) == \
                    "argparse.ArgumentParser":
                if arg_settings_inst in self._args:
                    self._args[arg_settings_inst][1].append(node.args[0])
                    for keyword in node.keywords:
                        self._args[arg_settings_inst][1].append(
                            ast.Assign(
                                targets=[ast.Name(id=keyword.arg)],
                                value = keyword.value, 
                                lineno = node.lineno,
                                col_offset = node.col_offset,
                                scopes = node.scopes))
                return None
        return node

