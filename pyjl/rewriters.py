from __future__ import annotations
import ast
import sys
from typing import Any, Dict

from py2many.exceptions import AstUnsupportedOperation
from py2many.inference import InferTypesTransformer
from py2many.tracer import find_closest_scope, find_in_scope, is_class_or_module, is_enum
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
        self._import_list = []
        self._import_count = 0
        self._ignored_module_set = \
            self._ignored_module_set = IGNORED_MODULE_SET.copy()\
                .union(JL_IGNORED_MODULE_SET.copy())
        self._class_fields: Dict[str, Any] = {}
        self._nested_classes = []

    def visit_Module(self, node: ast.Module) -> Any:
        self._hierarchy_map = {}
        self._import_list = []
        self._import_count = 0
        self._nested_classes = []

        node.lineno = 0
        node.col_offset = 0

        # Visit body nodes
        body = []
        for n in node.body:
            self._class_fields = {}
            if isinstance(n, ast.ClassDef):
                class_body = []
                for d in n.body:
                    if isinstance(d, ast.FunctionDef):
                        if d.name in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
                            JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE[d.name](
                                self, d)
                        else:
                            d.self_type = n.name
                            class_body.append(self.visit(d))
                    else:
                        class_body.append(self.visit(d))
                fields = []
                for f in self._class_fields.values():
                    if f is not None:
                        fields.append(f)
                n.body = fields + class_body

            b_node = self.visit(n)

            if self._nested_classes:                    
                for cls in self._nested_classes:
                    body.append(self.visit(cls))
                self._nested_classes = []

            body.append(b_node)

        # Create abstract types
        abstract_types = []
        l_no = self._import_count
        for (class_name, (extends_lst, is_jlClass)) in self._hierarchy_map.items():
            # node.class_names.append(class_name)
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
                if is_class_or_module(name, node.scopes) or name in self._import_list:
                    b = ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)
                    if b not in new_bases:
                        new_bases.append(b)
                else:
                    new_bases.append(base)
                extends.append(name)
            node.jl_bases = new_bases

        self._hierarchy_map[class_name] = (extends, is_jlClass)

        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
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

        return self.generic_visit(node)

    # TODO: Rewrite special method calls
    # def visit_Call(self, node: ast.Call) -> Any:
    #     fname = node.func
    #     if fname in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
    #         pass
    #     return node

    def visit_Expr(self, node: ast.Expr) -> Any:
        parent = node.scopes[-1]
        # Initialize class expression with None type
        if isinstance(parent, ast.ClassDef) and (id := get_id(node.value)):
            self._class_fields[id] = None
        return self.generic_visit(node)

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

    def visit_Import(self, node: ast.Import) -> Any:
        self._generic_import_visit(node)
        return self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        self._generic_import_visit(node)
        return self.generic_visit(node)

    def _generic_import_visit(self, node):
        is_visit = False
        for alias in node.names:
            alias_id = alias.name
            if alias_id not in self._ignored_module_set:
                is_visit = True
                if asname := getattr(alias, "asname", None):
                    self._import_list.append(asname)
                elif name := getattr(alias, "name", None):
                    self._import_list.append(name)

        if is_visit:
            self._import_count += 1


class JuliaAugAssignRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        requires_lowering = (
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
                    call.args.extend([node.target.value, node.target.slice, value])
                    return call
                elif not self._is_number(node.value) and isinstance(node.op, ast.Add):
                    old_slice: ast.Slice = node.target.slice
                    lower = old_slice.lower
                    upper = old_slice.upper
                    if (isinstance(lower, ast.Constant) and 
                                ((isinstance(lower, str) and lower.value.isdigit()) or
                                isinstance(lower, int))) or \
                            isinstance(lower, ast.Num):
                        lower = ast.Constant(value = int(lower.value) + 1)
                    else:
                        lower.splice_increment = True
                    new_slice = ast.Slice(
                        lower = lower,
                        upper = upper
                    )
                    call.args.extend([node.target.value, new_slice, node.value])
                    return call

            return ast.Assign(
                targets=[node.target],
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
                                scopes = [],
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

class JuliaSliceRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self.generic_visit(node)
        if lower := getattr(node.slice, "lower", None):
            if isinstance(lower, ast.UnaryOp) \
                    and isinstance(lower.op, ast.USub):
                node.slice.lower = ast.BinOp(
                    left = ast.Call(
                        func = ast.Name(
                            id = "length",
                            lineno = node.lineno,
                            col_offset = node.col_offset),
                        args = [node.value],
                        keywords = [],
                        annotation = ast.Name(id="int"),
                        lineno = node.lineno,
                        col_offset = node.col_offset),
                    op = ast.Sub(),
                    right = lower.operand,
                    lineno = node.lineno,
                    col_offset = node.col_offset)

        return node

###########################################################
################## Conditional Rewriters ##################
###########################################################

class ForLoopTargetRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
    
    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "optimize_loop_target", False):
            self._generic_scope_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_visit(node)
        return node
    
    def _generic_scope_visit(self, node):
        body = []
        for n in node.body:
            self.visit(n)
            if isinstance(n, ast.For):
                if getattr(node, "targets_out_of_scope", None):
                    target_id = get_id(n.target)
                    annotation = getattr(n.scopes.find(n.target), "annotation", None)
                    target = ast.Name(
                                id = target_id,
                                annotation = annotation)
                    assign = ast.Assign(
                        targets=[target],
                        value = ast.Constant(value = None),
                        # annotation = ast.Name(id= "int"),
                        lineno = n.lineno - 1,
                        col_offset = n.col_offset)
                    body.append(assign)
                    new_loop_id = f"_{target_id}"
                    new_var_assign = ast.Assign(
                        targets=[target],
                        value = ast.Name(
                            id = new_loop_id,
                            annotation = annotation),
                        # annotation = annotation,
                        lineno = n.lineno + 1,
                        col_offset = n.col_offset)
                    n.target.id = new_loop_id
                    n.body.insert(0, new_var_assign)

            body.append(n)
            
        # Update node body
        node.body = body
        
        return node

class JuliaOffsetArrayRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._offset_array_func = False
        self._list_args = set()
        self._subscript_vals = set()
        self._using_offset_arrays = False

    def visit_Module(self, node: ast.Module) -> Any:
        if getattr(node, "offset_arrays", False):
            self._using_offset_arrays = True
            self.generic_visit(node)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        if self._offset_array_func:
            ann = getattr(node.value, "annotation", None)
            ann_str:str = get_ann_repr(ann)
            if ann_str.startswith("List"):
                for n in node.targets:
                    self._list_args.add(get_id(n))
                node.value = self._build_offset_array_call(
                    node.value, ann, node.lineno, node.col_offset, 
                    node.scopes)
        return node
    
    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        self.generic_visit(node)
        if self._offset_array_func:
            ann: str = get_ann_repr(node.annotation)
            if ann.startswith("List"):
                self._list_args.add(get_id(node.target))
                node.value = self._build_offset_array_call(
                    node.value, node.annotation, node.lineno, 
                    node.col_offset, node.scopes)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self.generic_visit(node)
        if self._offset_array_func and (id := get_id(node.value)):
            self._subscript_vals.add(id)
            node.using_offset_arrays = True
            if isinstance(node.slice, ast.Slice):
                node.slice.using_offset_arrays = True
        return node

    def visit_Return(self, node: ast.Return) -> Any:
        if isinstance(node.value, ast.Name) and \
                get_id(node.value) in self._list_args:
            return ast.Call(
                func=ast.Name(id = "parent"),
                args = [node.value],
                keywords = [],
                annotation = node.value.annotation)
        return node

    def visit_For(self, node: ast.For) -> Any:
        self.generic_visit(node)
        if self._offset_array_func:
            node.iter.using_offset_arrays = True
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        parsed_decorators: Dict[str, Dict[str, str]] = node.parsed_decorators
        if not (OFFSET_ARRAYS in parsed_decorators and self._offset_arrays):
            return node

        # Get list args
        args = set()
        for a in node.args.args:
            annotation: str = get_ann_repr(a.annotation)
            if annotation and annotation.startswith("List"):
                args.add(a)

        # Visit body 
        return_node = None
        body = []
        self._offset_array_func = True
        for n in node.body:
            self.visit(n)
            if isinstance(n, ast.Return):
                return_node = n
            else:
                body.append(n)

        self._offset_array_func = False

        assignments = []
        for arg in args:
            arg_id = arg.arg
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
            assignments.append(assign)
        
        if assignments:
            let_stmt = juliaAst.LetStmt(
                    args = assignments,
                    body = body,
                    ctx = ast.Load(),
                    lineno = node.lineno + 1,
                    col_offset = node.col_offset
                )
            node.body = [let_stmt, return_node]

        return node


    def _build_offset_array_call(self, list_arg, annotation, lineno, col_offset, scopes):
        annotation = ast.Subscript(
            value = ast.Name(id="OffsetArray"),
            slice = annotation)
        return ast.Call(
                func = ast.Name(id="OffsetArray"),
                args = [list_arg, ast.Constant(-1)],
                keywords = [],
                annotation = annotation,
                lineno = lineno,
                col_offset = col_offset, 
                scopes = scopes
            )
