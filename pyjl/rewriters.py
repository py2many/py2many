from __future__ import annotations
import ast
import copy
import pickle
import sys
from typing import Any, Dict

from libcst import Call

from py2many.exceptions import AstUnsupportedOperation
from py2many.inference import InferTypesTransformer
from py2many.scope import ScopeList
from py2many.tracer import find_closest_scope, find_in_scope, find_node_by_name_and_type, is_class_or_module, is_class_type, is_enum
from py2many.analysis import IGNORED_MODULE_SET

from py2many.ast_helpers import get_id
from pyjl.clike import JL_IGNORED_MODULE_SET
from pyjl.global_vars import CHANNELS, OFFSET_ARRAYS, REMOVE_NESTED, RESUMABLE
from pyjl.helpers import generate_var_name, get_ann_repr
import pyjl.juliaAst as juliaAst
from pyjl.plugins import JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE


class JuliaMethodCallRewriter(ast.NodeTransformer):

    def __init__(self) -> None:
        super().__init__()
        self._ignored_module_set = JL_IGNORED_MODULE_SET

    def visit_Call(self, node):
        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]

        fname = node.func
        if isinstance(fname, ast.Attribute):
            new_func_name = fname.attr

            if get_id(fname.value):
                node0 = ast.Name(id=get_id(fname.value), lineno=node.lineno)
            else:
                node0 = fname.value

            args = [node0] + node.args

            node.func = ast.Name(
                id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        node.args = args
        return self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        value_id = None
        if node_id := get_id(node.value):
            value_id = node_id
        elif isinstance(node.value, ast.Call)\
                and (call_id := get_id(node.value.func)):
            value_id = call_id

        if value_id and value_id not in sys.builtin_module_names \
                and value_id not in self._ignored_module_set \
                and (is_enum(value_id, node.scopes) or
                     is_class_or_module(value_id, node.scopes) or
                     is_class_type(value_id, node.scopes) or
                     # is_class_type(value_id, node.scopes) or
                     value_id.startswith("self")):
            return node

        return ast.Call(
            func=ast.Name(id=node.attr, ctx=ast.Load()),
            args=[node.value],
            keywords=[],
            lineno=node.lineno,
            col_offset=node.col_offset)


class JuliaClassRewriter(ast.NodeTransformer):
    """Transforms Python classes into Julia compatible classes"""

    def __init__(self) -> None:
        super().__init__()
        self._hierarchy_map = {}
        self._import_count = 0
        self._ignored_module_set = \
            self._ignored_module_set = IGNORED_MODULE_SET.copy()\
                .union(JL_IGNORED_MODULE_SET.copy())
        self._class_fields: Dict[str, Any] = {}
        self._nested_classes = []
        self._class_scopes = []
        self._current_class_scope = None

    def visit_Module(self, node: ast.Module) -> Any:
        self._hierarchy_map = {}
        self._import_count = 0
        self._nested_classes = []
        self._class_scopes = []

        node.lineno = 0
        node.col_offset = 0

        # Visit body nodes
        body = []
        for n in node.body:
            self.visit(n)
            if self._nested_classes:
                # Add nested classes to top scope                 
                for cls in self._nested_classes:
                    body.append(self.visit(cls))
                self._nested_classes = []

            body.append(n)

        # Create abstract types
        abstract_types = []
        l_no = self._import_count
        for (class_name, (extends_lst, is_jlClass)) in self._hierarchy_map.items():
            if not is_jlClass:
                core_module = extends_lst[0].split(
                    ".")[0] if extends_lst else None
                # TODO: Investigate Julia traits
                nameVal = ast.Name(id=class_name)
                extends = ast.Name(id=f"Abstract{extends_lst[0]}") \
                    if extends_lst and core_module not in self._ignored_module_set \
                    else None
                abstract_types.append(
                    juliaAst.AbstractType(value=nameVal, extends=extends,
                                          ctx=ast.Load(), lineno=l_no, col_offset=0))
                # increment linenumber
                l_no += 1

        if abstract_types:
            body = body[:self._import_count] + \
                abstract_types + body[self._import_count:]

        node.body = body

        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        class_name: str = get_id(node)

        # Get new class scope
        self._class_scopes.append(self._current_class_scope)
        self._current_class_scope = class_name

        decorator_list = list(map(get_id, node.decorator_list))
        is_jlClass = "jl_class" in decorator_list

        extends = []
        if not node.bases or len(node.bases) == 0:
            node.jl_bases = [
                ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]
        elif len(node.bases) == 1:
            name = get_id(node.bases[0])
            node.jl_bases = [
                ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]
            extends = [name]
        elif len(node.bases) > 1:
            # TODO: Investigate Julia traits
            new_bases = []
            for base in node.bases:
                name = get_id(base)
                if is_class_or_module(name, node.scopes):
                    b = ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)
                    if b not in new_bases:
                        new_bases.append(b)
                else:
                    new_bases.append(base)
                extends.append(name)
            node.jl_bases = new_bases

        self._hierarchy_map[class_name] = (extends, is_jlClass)

        self._class_fields = {}
        self.generic_visit(node)

        # Get new class fields
        fields = []
        for f in self._class_fields.values():
            if f is not None:
                fields.append(f)
        node.body = fields + node.body

        # Go back to old scope
        self._current_class_scope = self._class_scopes.pop()

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self.generic_visit(node)

        func_name = get_id(node)
        if func_name in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
            return JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE[func_name](self, node)
        
        # Add self type
        node.self_type = self._current_class_scope

        args = node.args
        for arg in args.args:
            if ((annotation := getattr(arg, "annotation", None)) and
                    is_class_or_module(annotation, node.scopes)):
                setattr(annotation, "id", f"Abstract{annotation}")

        if (hasattr(node, "self_type") and
                is_class_or_module(node.self_type, node.scopes)):
            node.self_type = f"Abstract{node.self_type}"

        # Remove any classes from function body 
        # if @remove_nested decorator is present
        body = []
        for n in node.body:
            if isinstance(n, ast.ClassDef) and \
                    REMOVE_NESTED in n.parsed_decorators:
                self._nested_classes.append(n)
            else:
                body.append(self.visit(n))

        node.body = body

        return node

    # TODO: Rewrite special method calls
    # def visit_Call(self, node: ast.Call) -> Any:
    #     fname = node.func
    #     if fname in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
    #         pass
    #     return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        target = node.targets[0]
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        target = node.target
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def _generic_assign_visit(self, node, target):
        if self._is_member(target):
            if target.attr not in self._class_fields:
                self._class_fields[target.attr] = node
            else:
                class_field = self._class_fields[target.attr]
                if class_field.value is None and node.value:
                    self._class_fields[target.attr] = node

    def _is_member(self, node):
        return hasattr(node, "value") and get_id(node.value) == "self"


class JuliaAugAssignRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        is_class = is_class_type(get_id(node.target), node.scopes) or \
            is_class_type(get_id(node.value), node.scopes)
        requires_lowering = (
            is_class or
            isinstance(node.op, ast.BitXor) or
            isinstance(node.op, ast.BitAnd) or
            ((isinstance(node.op, ast.Add) or
              isinstance(node.op, ast.Mult) or
              isinstance(node.op, ast.MatMult)) and
                (self._is_list(node.target) or
                 self._is_list(node.value)))
        )
        if requires_lowering:
            # New binary operation
            value = ast.BinOp(
                    left=node.target,
                    op=node.op,
                    right=node.value,
                    lineno=node.lineno,
                    col_offset=node.col_offset)

            node_target = node.target
            if isinstance(node.target, ast.Subscript):
                # TODO: This is an expensive operation
                node_target = copy.deepcopy(node.target)

            if isinstance(node.target, ast.Subscript) and \
                    isinstance(node.target.slice, ast.Slice):
                # Replace node with a call
                call = ast.Call(
                    func = ast.Name(
                        id = "splice!",
                        lineno = node.lineno,
                        col_offset = node.col_offset),
                    args = [],
                    keywords = [],
                    lineno = node.lineno,
                    col_offset = node.col_offset)

                if self._is_number(node.value) and isinstance(node.op, ast.Mult):
                    call.args.extend([node_target.value, node_target.slice, value])
                    return call
                elif not self._is_number(node.value) and isinstance(node.op, ast.Add):
                    old_slice: ast.Slice = copy.deepcopy(node_target.slice)
                    lower = old_slice.lower
                    upper = old_slice.upper
                    if isinstance(lower, ast.Constant) and isinstance(lower.value, int) :
                        lower = ast.Constant(value = int(lower.value) + 1)
                    # else:
                    #     lower.splice_increment = True
                    new_slice = ast.Slice(
                        lower = lower,
                        upper = upper
                    )
                    call.args.extend([node_target.value, new_slice, node.value])
                    return call


            return ast.Assign(
                targets=[node_target],
                value = value,
                lineno=node.lineno,
                col_offset=node.col_offset
            )

        return self.generic_visit(node)

    @staticmethod
    def _is_list(node):
        annotation = getattr(node, "annotation", None)
        if annotation:
            return get_ann_repr(annotation).startswith("List")
        return False

    @staticmethod
    def _is_number(node):
        return isinstance(node, ast.Num) or \
                (isinstance(node, ast.Constant) and node.value.isdigit()) or \
                (get_id(getattr(node, "annotation", None)) in 
                    InferTypesTransformer.FIXED_WIDTH_INTS)


class JuliaGeneratorRewriter(ast.NodeTransformer):
    def __init__(self):
        self._generator_funcs = {}
        self._assign_map = {}
        self._nested_funcs = []
        self._resumables_assigns = []
        super().__init__()

    def visit_Module(self, node: ast.Module) -> Any:
        body = []
        for n in node.body:
            b_node = self.visit(n)
            if isinstance(n, ast.FunctionDef):
                self._nested_funcs = []
                if self._nested_funcs:
                    for nested in self._nested_funcs:
                        body.append(self.visit(nested))

            body.append(b_node)

        node.body = body

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        # self.generic_visit(node)
        yield_node = find_in_scope(
            node.body, lambda x: isinstance(x, ast.Yield))

        body = []
        for n in node.body:
            if isinstance(n, ast.FunctionDef) and RESUMABLE in n.parsed_decorators:
                resumable = n.parsed_decorators[RESUMABLE]
                if REMOVE_NESTED in resumable \
                        and resumable[REMOVE_NESTED]:
                    self._nested_funcs.append(n)
                    continue

            visit_node = self.visit(n)
            if self._resumables_assigns:
                for assert_node in self._resumables_assigns:
                    body.append(assert_node)
                self._resumables_assigns = []
            
            body.append(visit_node)

        node.body = body

        if RESUMABLE in node.parsed_decorators and \
                CHANNELS in node.parsed_decorators:
            raise AstUnsupportedOperation(  
                "Function cannot have both @resumable and @channels decorators", 
                node)

        is_resumable = RESUMABLE in node.parsed_decorators
        self._generator_funcs[node.name] = is_resumable
        if yield_node and not is_resumable:
            # Body contains yield and is not resumable function
            node.returns_channel = True
            node.body = [
                ast.With(
                    items = [
                        ast.withitem(
                            context_expr = ast.Call(
                                func=ast.Name(
                                    id = "Channel",
                                    lineno = node.lineno,
                                    col_offset = node.col_offset),
                                args = [],
                                keywords = [],
                                scopes = ScopeList(),
                                lineno = node.lineno,
                                col_offset = node.col_offset),
                            optional_vars = ast.Name(
                                id = f"ch_{node.name}",
                                lineno = node.lineno,
                                col_offset = node.col_offset)
                        )
                    ],
                    body = node.body,
                    lineno = node.lineno,
                    col_offset = node.col_offset)
            ]

        return node

    def visit_YieldFrom(self, node: ast.YieldFrom) -> Any:
        parent = find_closest_scope(node.scopes)
        if isinstance(parent, ast.FunctionDef):
            dec = None
            if CHANNELS in parent.parsed_decorators:
                dec = parent.parsed_decorators[CHANNELS]
            elif RESUMABLE in parent.parsed_decorators:
                dec = parent.parsed_decorators[RESUMABLE]
            lower_yield_from = dec and dec["lower_yield_from"]
            if lower_yield_from:
                common_loop_vars = ["v", "w", "x", "y", "z"]
                val = ast.Name(
                        id = generate_var_name(parent, common_loop_vars),
                        lineno = node.lineno,
                        col_offset = node.col_offset)
                new_node = ast.For(
                    target = val,
                    iter = node.value,
                    body = [
                        ast.Yield(
                            value = val
                        )],
                    lineno = node.lineno,
                    col_offset = node.col_offset)
                return new_node

        return self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        if isinstance(node.value, ast.List) or isinstance(node.value, ast.Tuple):
            value_list = map(lambda x: get_id(x.func) if isinstance(x, ast.Call) else None, node.value.elts)
            for target, value in zip(node.targets, value_list):
                if value and (t_id := get_id(target)):
                    self._assign_map[t_id] = value
        else:
            if isinstance(node.value, ast.Call):
                for target in node.targets:
                    if t_id := get_id(target):
                        self._assign_map[t_id] = get_id(node.value.func)

        return node

    # TODO: Creating assignments for resumable func calls. Does not work
    # def visit_Call(self, node: ast.Call) -> Any:
    #     self.generic_visit(node)
    #     parent = find_closest_scope(node.scopes)
    #     if (id := get_id(node.func)) and len(node.args) > 0:
    #         if id in self._generator_funcs \
    #                 and self._generator_funcs[id]:
    #             if not getattr(parent, "has_generator_assign", None):
    #                 # Create new assignment node for resumable
    #                 new_node = ast.Assign(
    #                     targets = [
    #                         ast.Name(
    #                             id=f"{id}_var",
    #                             lineno = node.lineno,
    #                             col_offset = node.col_offset)
    #                     ],
    #                     value = ast.Call(
    #                         func = node.func,
    #                         args = node.args.copy(),
    #                         keywords = node.keywords,
    #                         scopes = node.scopes,
    #                         lineno = node.lineno,
    #                         col_offset = node.col_offset
    #                     ),
    #                     lineno = node.lineno,
    #                     col_offset = node.col_offset)

    #                 self._resumables_assigns.append(new_node)
    #                 parent.has_generator_assign = True

    #             node.func = ast.Name(
    #                 id= f"{id}_var",
    #                 lineno = node.lineno,
    #                 col_offset = node.col_offset)
    #             node.args = []
    #     return node

# TODO: More a transformer than a rewriter
class JuliaDecoratorRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def _parse_decorators(self, node):
        parsed_decorators: Dict[str, Dict[str, str]] = {}
        if decorator_list := getattr(node, "decorator_list", None):
            for decorator in decorator_list:
                if isinstance(decorator, ast.Name):
                    parsed_decorators[get_id(decorator)] = None
                elif isinstance(decorator, ast.Call):
                    keywords = {}
                    for keyword in decorator.keywords:
                        keywords[keyword.arg] = keyword.value.value
                    parsed_decorators[get_id(decorator.func)] = keywords
                
        if "dataclass" in parsed_decorators \
                and "jl_dataclass" in parsed_decorators:
            parsed_decorators.pop("dataclass")

        node.parsed_decorators = parsed_decorators


class JuliaConditionRewriter(ast.NodeTransformer):
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
            node.test = ast.Compare(
                left = node.test,
                ops = [ast.NotEq()],
                comparators = [
                    ast.Constant(
                        0, 
                        lineno = node.test.lineno,
                        col_offset = node.test.col_offset)
                    ],
                lineno = node.test.lineno,
                col_offset = node.test.col_offset
            )

class JuliaIndexingRewriter(ast.NodeTransformer):

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

    def __init__(self) -> None:
        super().__init__()
        self._curr_slice_val = None
        self._imports = []

    def visit_Module(self, node: ast.Module) -> Any:
        imports = getattr(node, "imports", [])
        self._imports = [get_id(a) for a in imports]
        self.generic_visit(node)
        return node

    def visit_LetStmt(self, node: juliaAst.LetStmt):
        # Introduced in JuliaOffsetArrayRewriter
        for a in node.args:
            self.visit(a)
        for n in node.body:
            self.visit(n)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        # Don't rewrite nodes that are annotations
        if hasattr(node, "is_annotation"):
            return node

        self._curr_slice_val = node.value
        self.generic_visit(node)
        self._curr_slice_val = None
        value_id = get_id(node.value)

        # Handle negative indexing 
        if isinstance(node.slice, ast.UnaryOp) and \
                isinstance(node.slice.op, ast.USub) and \
                isinstance(node.slice.operand, ast.Constant):
            end_val = ast.Name(
                    id = "end",
                    lineno = node.lineno,
                    col_offset = node.col_offset,
                    annotation = ast.Name(id="int"),
                    preserve_keyword = True)
            if node.slice.operand.value == 1:
                node.slice = end_val
            else:
                node.slice = ast.BinOp(
                    left = end_val,
                    op = ast.Sub(),
                    right = ast.Constant(value = node.slice.operand.value - 1),
                    annotation = ast.Name(id = "int")
                )

        if not self._is_dict(node, value_id) and \
                not isinstance(node.slice, ast.Slice):
            call_id = self._get_func_name(node)
            if not getattr(node, "range_optimization", None) and \
                    not getattr(node, "using_offset_arrays", None):
                # Ignore special functions, as they already return the correct indices
                if call_id in self.SPECIAL_FUNCTIONS and \
                        call_id in self._imports:
                    return node

                if isinstance(node.slice, ast.Constant) \
                        and isinstance(node.slice.value, int):
                    # Shortcut if index is a numeric value
                    node.slice.value += 1 
                else:
                    # Default: add 1
                    if get_id(node.slice) != "end":
                        node.slice = self._do_bin_op(node.slice, ast.Add(), 1,
                            node.lineno, node.col_offset)
            else:
                if call_id in self.SPECIAL_FUNCTIONS:
                    node.slice = self._do_bin_op(node.slice, ast.Add(), 1,
                        node.lineno, node.col_offset)

        return node

    def _get_func_name(self, node: ast.Subscript):
        call_id = None
        if isinstance(node.slice, ast.Call):
            call_id = get_id(node.slice.func)
            assign_node = find_node_by_name_and_type(call_id, ast.Assign, node.scopes)[0]
            if assign_node:
                if isinstance(assign_node.value, ast.Call):
                    call_id = get_id(assign_node.value.func)
                elif id := get_id(assign_node.value):
                    call_id = id 
        return call_id

    def visit_Slice(self, node: ast.Slice) -> Any:
        self.generic_visit(node)

        # Might need this later
        # elif getattr(node.lower, "splice_increment", None):
        #     # From JuliaAugAssignRewriter
        #     lower = f"({lower} + 2)"

        if isinstance(node.lower, ast.UnaryOp) \
                and isinstance(node.lower.op, ast.USub) \
                and self._curr_slice_val:
            node.lower = ast.BinOp(
                left = ast.Call(
                    func = ast.Name(
                        id = "length",
                        lineno = node.lineno,
                        col_offset = node.col_offset,
                        annotation = ast.Name(id = "int")),
                    args = [self._curr_slice_val],
                    keywords = [],
                    annotation = ast.Name(id="int"),
                    lineno = node.lineno,
                    col_offset = node.col_offset),
                op = ast.Sub(),
                right = node.lower.operand,
                lineno = node.lineno,
                col_offset = node.col_offset)

        # Julia array indices start at 1
        if isinstance(node.lower, ast.Constant) and node.lower.value == -1:
            node.lower = ast.Name(
                id = "end",
                lineno = node.lineno,
                col_offset = node.col_offset,
                annotation = ast.Name(id="int"))
        elif not getattr(node, "range_optimization", None) and \
                not getattr(node, "using_offset_arrays", None):
            if isinstance(node.lower, ast.Constant) and isinstance(node.lower.value, int):
                node.lower.value += 1
            elif node.lower:
                # Default: add 1
                node.lower = self._do_bin_op(node.lower, ast.Add(), 1,
                    node.lineno, node.col_offset)

        if hasattr(node, "step"):
            # Cover Python list reverse
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
                if len(node.args) > 1:
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
                    # Switch args
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
                        annotation = ast.Name(id= "int")),
                    lineno = lineno,
                    col_offset = col_offset
                )

    def _is_dict(self, node, value_id):
        val = node.scopes.find(value_id)
        annotation = getattr(val, "annotation", None)
        return (isinstance(annotation, ast.Subscript) and
                    get_id(annotation.value) == "Dict") or \
                (isinstance(annotation, ast.Name)
                    and get_id(annotation) == "Dict")


###########################################################
################## Conditional Rewriters ##################
###########################################################

class ForLoopTargetRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._targets_out_of_scope = False
        self._target_vals: list[tuple] = []
    
    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "optimize_loop_target", False):
            self._generic_scope_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_visit(node)
        return node
    
    def _generic_scope_visit(self, node):
        body = []
        target_state = self._targets_out_of_scope
        self._targets_out_of_scope = getattr(node, "targets_out_of_scope", None)
        for n in node.body:
            self.visit(n)
            if self._target_vals:
                for target, default in self._target_vals:
                    assign = ast.Assign(
                        targets=[target],
                        value = ast.Constant(value = default),
                        # annotation = ast.Name(id= "int"),
                        lineno = node.lineno - 1,
                        col_offset = node.col_offset)
                body.append(assign)
                self._target_vals = []

            body.append(n)
            
        # Update node body
        node.body = body
        self._targets_out_of_scope = target_state
        
        return node
    
    def visit_For(self, node: ast.For) -> Any:
        if self._targets_out_of_scope:
            # Get target and its default value
            target_id = get_id(node.target)
            target_default = self._get_default_val_from_iter(node.iter)
            self._target_vals.append((ast.Name(target_id), target_default))

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
                col_offset = node.col_offset)
            node.target.id = new_loop_id
            node.body.insert(0, new_var_assign)
        return node

    # TODO: get more use-cases
    def _get_default_val_from_iter(self, iter):
        if isinstance(iter, ast.Call) and get_id(iter.func) == "range":
            return 0
        return None

# TODO: Still preliminary
class JuliaOffsetArrayRewriter(ast.NodeTransformer):

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
            annotation: str = get_ann_repr(arg.annotation)
            # TODO: Optimize: "arg_id not in self._subscript_vals" (This is O(n^2))
            if not annotation or (annotation and not annotation.startswith("List"))\
                    or arg_id not in self._subscript_vals:
                continue
            arg_name = ast.Name(id=arg_id)
            val = self._build_offset_array_call(
                        arg_name, arg.annotation, node.lineno, 
                        node.col_offset, node.scopes)
            assign = ast.Assign(
                    targets = [arg_name],
                    value = val,
                    annotation = val.annotation, 
                    lineno = node.lineno + 1,
                    col_offset = node.col_offset,
                    scopes = node.scopes # TODO: Remove the return statement form scopes
                )
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
        if self._use_offset_array and self._is_list(ann):
            for n in node.targets:
                if id := get_id(n):
                    self._list_assigns.append(id)
            if not isinstance(node.value, ast.List):
                node.value = self._build_offset_array_call(
                    node.value, ann, node.lineno, 
                    node.col_offset, node.scopes)
        self._is_assign_val = True
        self.generic_visit(node)
        self._is_assign_val = False
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        node.target.require_parent = False
        if self._use_offset_array and self._is_list(node.annotation):
            # node.annotation = ast.Name(id="OffsetArray")
            self._list_assigns.append(get_id(node.target))
            if not isinstance(node.value, ast.List):
                node.value = self._build_offset_array_call(
                    node.value, node.annotation, node.lineno, 
                    node.col_offset, node.scopes)
        self._is_assign_val = True
        self.generic_visit(node)
        self._is_assign_val = False
        return node

    def _is_list(self, annotation):
        ann_str:str = get_ann_repr(annotation)
        return ann_str and (ann_str.startswith("List") \
            or ann_str.startswith("list"))

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        node.value.require_parent = False
        self.generic_visit(node)

        # Cover nested subscripts
        if isinstance(node.value, ast.Subscript):
            node.using_offset_arrays = node.value.using_offset_arrays

        if self._use_offset_array and (id := get_id(node.value)):
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
                func = ast.Name(id="OffsetArray"),
                args = [list_arg, ast.Constant(-1)],
                keywords = [],
                annotation = annotation,
                lineno = lineno,
                col_offset = col_offset, 
                scopes = scopes
            )

    def _create_parent(self, node, lineno, col_offset):
        # TODO: Unreliable annotations when calling parent
        arg_id = get_id(node)
        new_annotation = getattr(self._current_scope.find(arg_id), "annotation", None)
        return ast.Call(
            func=ast.Name(id = "parent"),
            args = [node],
            keywords = [],
            annotation = new_annotation,
            lineno = lineno,
            col_offset = col_offset if col_offset else 0,
            scopes = self._current_scope)
