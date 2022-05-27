from __future__ import annotations, nested_scopes
import ast
from calendar import c
import copy
import os
import sys
from typing import Any, Dict

from py2many.exceptions import AstUnsupportedOperation
from py2many.inference import InferTypesTransformer
from py2many.scope import ScopeList
from py2many.tracer import find_closest_scope, find_node_by_name_and_type, is_class_or_module, is_class_type, is_enum, is_list
from py2many.analysis import IGNORED_MODULE_SET, is_mutable

from py2many.ast_helpers import copy_attributes, get_id
from pyjl.clike import JL_IGNORED_MODULE_SET
from pyjl.global_vars import CHANNELS, OFFSET_ARRAYS, REMOVE_NESTED, RESUMABLE, USE_MODULES
from pyjl.helpers import generate_var_name, get_ann_repr, get_func_def, obj_id
import pyjl.juliaAst as juliaAst
from pyjl.plugins import JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE


class JuliaMethodCallRewriter(ast.NodeTransformer):
    """Converts Python calls and attribute calls to Julia compatible ones"""
    def __init__(self) -> None:
        super().__init__()
        self._ignored_module_set = JL_IGNORED_MODULE_SET
        self._imports = []
        self._file = None
        self._use_modules = None

    def visit_Module(self, node: ast.Module) -> Any:
        self._file = getattr(node, "__file__", ".")
        self._use_modules = getattr(node, USE_MODULES, None)
        self._imports = list(map(get_id, getattr(node, "imports", [])))
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        # Don't parse annotations
        if hasattr(node, "is_annotation"):
            return node

        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]

        fname = node.func
        if isinstance(fname, ast.Attribute):
            if get_id(fname.value) in self._imports and not self._use_modules:
                # Handle separate module call when Julia defines no 'module'
                new_func_name = fname.attr
                node.func = ast.Name(
                    id=new_func_name, lineno=node.lineno, ctx=fname.ctx)
            elif not is_class_or_module(get_id(fname.value), node.scopes):
                self._handle_special_cases(fname)

                value_id = get_id(fname.value)
                if value_id:
                    node0 = ast.Name(id=value_id, lineno=node.lineno)
                else:
                    node0 = fname.value

                args = [node0] + node.args

                new_func_name = fname.attr
                node.func = ast.Name(
                    id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        node.args = args
        return self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        self.generic_visit(node)
        
        # Don't parse annotations
        if hasattr(node, "is_annotation"):
            return node

        if ret := self._handle_special_cases(node):
            return ret

        value_id = None
        if node_id := get_id(node.value):
            value_id = node_id
        elif isinstance(node.value, ast.Call)\
                and (call_id := get_id(node.value.func)):
            value_id = call_id

        if value_id and value_id not in sys.builtin_module_names \
                and value_id not in self._ignored_module_set \
                and (is_enum(value_id, node.scopes) or
                    ((is_class_or_module(value_id, node.scopes) or
                    is_class_type(value_id, node.scopes))
                    and self._use_modules) or
                    value_id.startswith("self")):
            return node

        annotation = getattr(node.scopes.find(get_id(node.value)), "annotation", None)

        node.dispatch = ast.Call(
            func=ast.Name(id=node.attr, ctx=ast.Load()),
            args=[node.value],
            keywords=[],
            lineno=node.lineno,
            col_offset=node.col_offset,
            annotation = annotation,
            scopes = node.scopes,
            is_attr = True)

        return node

    def _handle_special_cases(self, node):
        # Bypass init module calls
        func_repr = get_id(node)
        split_repr = func_repr.split(".") if func_repr else []
        if split_repr and self._is_dir(split_repr):
            self._insert_init(node)
            return node

        # Bypass imports
        for i in range(1,len(split_repr)):
            if self._is_module(split_repr[:i]):
                return node

        return None

    def _insert_init(self, node):
        if isinstance(node.value, ast.Attribute):
            self._insert_init(node.value)
        else:
            # Avoid referencing the same object
            value = copy.deepcopy(node.value)
            node.value = ast.Attribute(
                value = value,
                attr = node.attr,
                ctx = ast.Load(),
                scopes = node.scopes,
                lineno = node.lineno,
                col_offset = node.col_offset
            )
            node.attr = "__init__"
            return node.value.value
    
    def _is_module(self, path: list[str]):
        path_str = os.sep.join(path)
        return path_str in self._imports

    def _is_dir(self, path: list[str]):
        path_str = os.sep.join(path)
        is_file = os.path.isdir(f"{os.getcwd()}{os.sep}{self._file}{os.sep}{path_str}")
        return is_file and path[-1] in self._imports


class JuliaClassRewriter(ast.NodeTransformer):
    """Transforms Python classes into Julia compatible classes"""

    def __init__(self) -> None:
        super().__init__()
        self._ignored_module_set = \
            self._ignored_module_set = IGNORED_MODULE_SET.copy()\
                .union(JL_IGNORED_MODULE_SET.copy())
        self._class_fields: Dict[str, Any] = {}
        self._hierarchy_map = {}
        self._nested_classes = []
        self._class_scopes = []

    def visit_Module(self, node: ast.Module) -> Any:
        self._hierarchy_map = {}
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
        l_no = node.import_cnt
        for (class_name, (extends_lst, is_jlClass)) in self._hierarchy_map.items():
            if not is_jlClass and extends_lst:
                core_module = extends_lst[0].split(
                    ".")[0] if extends_lst[0] else None
                # TODO: Investigate Julia traits
                nameVal = ast.Name(id=class_name)
                extends = None
                if extends_lst and core_module not in self._ignored_module_set:
                    extends_name = f"Abstract{extends_lst[0]}" \
                        if extends_lst[0] in self._hierarchy_map \
                        else extends_lst[0]
                    extends = ast.Name(id=f"{extends_name}") 
                abstract_types.append(
                    juliaAst.AbstractType(value=nameVal, extends = extends,
                                          ctx=ast.Load(), lineno=l_no, col_offset=0))
                # increment linenumber
                l_no += 1

        if abstract_types:
            body = body[:node.import_cnt] + \
                abstract_types + body[node.import_cnt:]

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

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self.generic_visit(node)

        func_name = get_id(node)
        if func_name in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
            return JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE[func_name](self, node)

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

    def visit_Call(self, node: ast.Call) -> Any:
        func = node.func
        if isinstance(func, ast.Attribute):
            value_id = get_id(func.value)
            val_node = find_node_by_name_and_type(value_id, ast.ClassDef, node.scopes)[0]
            if isinstance(val_node, ast.ClassDef):
                func_n = ast.Name(id=value_id, lineno=node.lineno) \
                    if value_id else func.value

                if func.attr == "__init__":
                    func_n.annotation = getattr(node.func, "annotation", None)
                    node.func = func_n
                    node.args = node.args[1:]
                    return node
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        if self._is_self(node.targets[0]):
            annotation = getattr(node.value, "annotation", None)
            if not annotation:
                annotation = ast.Constant(value="Any")
            for target in node.targets:
                target_id = obj_id(target)
                if target_id not in self._class_fields:
                    self._class_fields[target_id] = ast.AnnAssign(
                        target=ast.Name(id=target_id),
                        annotation = annotation,
                        lineno=1)
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        if self._is_self(node.target):
            target_id = obj_id(node.target)
            if target_id not in self._class_fields:
                self._class_fields[target_id] = ast.AnnAssign(
                        target=ast.Name(id=target_id),
                        annotation = node.annotation,
                        lineno=1)
        return node

    def _is_self(self, node):
        return isinstance(node, ast.Attribute) and get_id(node.value) == "self"


class JuliaAugAssignRewriter(ast.NodeTransformer):
    """Rewrites augmented assignments into assignments with
    binary operations. This is required in certain cases where
    Python uses operator overloading"""
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
                (is_list(node.target) or
                 is_list(node.value)))
        )
        if requires_lowering:
            # New binary operation
            value = ast.BinOp(
                    left=node.target,
                    op=node.op,
                    right=node.value,
                    lineno=node.lineno,
                    col_offset=node.col_offset,
                    scopes = node.value.scopes)

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
                    col_offset = node.col_offset,
                    scopes = node.target.lineno)

                if self._is_number(node.value) and isinstance(node.op, ast.Mult):
                    call.args.extend([node_target.value, node_target.slice, value])
                    return call
                elif not self._is_number(node.value) and isinstance(node.op, ast.Add):
                    old_slice: ast.Slice = copy.deepcopy(node_target.slice)
                    lower = old_slice.lower
                    upper = old_slice.upper
                    if isinstance(lower, ast.Constant) and isinstance(lower.value, int) :
                        lower = ast.Constant(value = int(lower.value) + 1, scopes = lower.scopes)
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


class JuliaGeneratorRewriter(ast.NodeTransformer):
    """A Rewriter for Generator functions"""
    SPECIAL_FUNCTIONS = set([
        "islice"
    ])

    def __init__(self):
        super().__init__()
        self._nested_funcs = []
        self._replace_map: Dict = {}
        self._replace_calls: Dict[str, ast.Call] = {}
        self._sweep = False

    def _visit_func_defs(self, node):
        for n in node.body:
            if isinstance(n, ast.FunctionDef):
                self.visit(n)

    def visit_Name(self, node: ast.Name) -> Any:
        self.generic_visit(node)
        if (id := get_id(node)) in self._replace_map:
            return self._replace_map[id]
        return node

    def visit_Module(self, node: ast.Module) -> Any:
        # Reset state
        self._replace_calls = {}
        self._replace_map: Dict = {}

        body = []
        for n in node.body:
            b_node = self.visit(n)
            if isinstance(n, ast.FunctionDef):
                self._nested_funcs = []
                if self._nested_funcs:
                    for nested in self._nested_funcs:
                        body.append(self.visit(nested))

            body.append(b_node)

        # Sweep phase
        self._sweep = True
        self.generic_visit(node)
        self._sweep = False
        
        # Update node body
        node.body = body


        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        if self._sweep:
            body = list(map(lambda x: self.visit(x), node.body))
            node.body = list(filter(lambda x: x is not None, body))
            return node

        body = []

        # Check if function uses resumables
        is_resumable = lambda x: RESUMABLE in x.parsed_decorators
        
        node.n_body = []
        for n in node.body:
            if isinstance(n, ast.FunctionDef) and is_resumable(n):
                resumable = n.parsed_decorators[RESUMABLE]
                if resumable and REMOVE_NESTED in resumable \
                        and resumable[REMOVE_NESTED]:
                    self._nested_funcs.append(n)
                    continue

            n_visit = self.visit(n)
            if node.n_body:
                body.extend(node.n_body)
                node.n_body = []
            if n_visit:
                body.append(n_visit)

        # Update body
        node.body = body

        if is_resumable(node) and \
                CHANNELS in node.parsed_decorators:
            raise AstUnsupportedOperation(  
                "Function cannot have both @resumable and @channels decorators", 
                node)

        ann_id = get_id(getattr(node, "annotation", None))
        if ann_id == "Generator" and not is_resumable(node):
            # Body contains yield and is not resumable function
            node.body = [
                ast.With(
                    items = [ast.withitem(
                        context_expr = ast.Call(
                            func=ast.Name(id = "Channel"),
                            args = [],
                            keywords = [],
                            scopes = ScopeList(),
                            lineno = node.lineno,
                            col_offset = node.col_offset),
                        optional_vars = ast.Name(id = f"ch_{node.name}"))],
                    body = node.body,
                    lineno = node.lineno,
                    col_offset = node.col_offset)]

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


# TODO: More a transformer than a rewriter
class JuliaDecoratorRewriter(ast.NodeTransformer):
    """Parses decorators and adds them to functions 
    and class scopes"""
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
                        if hasattr(keyword.value, "value"):
                            keywords[keyword.arg] = keyword.value.value
                        else:
                            keywords[keyword.arg] = keyword.value
                    parsed_decorators[get_id(decorator.func)] = keywords
                
        if "dataclass" in parsed_decorators \
                and "jl_dataclass" in parsed_decorators:
            parsed_decorators.pop("dataclass")

        node.parsed_decorators = parsed_decorators


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
            node.test = ast.Compare(
                left = node.test,
                ops = [ast.NotEq()],
                comparators = [
                    ast.Constant(
                        0,
                        lineno = node.test.lineno,
                        col_offset = node.test.col_offset,
                        scopes = node.test.scopes)],
                lineno = node.test.lineno,
                col_offset = node.test.col_offset,
                scopes = node.scopes
            )
    
    def visit_Compare(self, node: ast.Compare) -> Any:
        # Julia comparisons with 'None' or mutable vars use Henry Baker's EGAL predicate
        # https://stackoverflow.com/questions/38601141/what-is-the-difference-between-and-comparison-operators-in-julia
        self.generic_visit(node)
        find_none = lambda x: isinstance(x, ast.Constant) and x.value == None
        comps_none = next(filter(find_none, node.comparators), None)
        mutable_comps = next(filter(lambda x: is_mutable(node.scopes, get_id(x)), node.comparators), None)
        mutable_left = is_mutable(node.scopes, get_id(node.left))
        if find_none(node.left) or comps_none or \
                mutable_comps or mutable_left:
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

        # Handle negative indexing 
        if isinstance(node.slice, ast.UnaryOp) and \
                isinstance(node.slice.op, ast.USub) and \
                isinstance(node.slice.operand, ast.Constant):
            end_val = ast.Name(
                    id = "end",
                    annotation = ast.Name(id="int"),
                    preserve_keyword = True)
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
                    col_offset = node.col_offset,
                    scopes = node.lower.scopes),
                op = ast.Sub(),
                right = node.lower.operand,
                lineno = node.lineno,
                col_offset = node.col_offset,
                scopes = node.lower.scopes)

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
        if is_main:
            node.python_main = is_main
            node.test.left = ast.Call(
                func = ast.Name(id="abspath"),
                args = [ast.Name(id="PROGRAM_FILE")],
                keywords = [],
                scopes = node.test.left.scopes,
                lineno = node.test.left.lineno,
                col_offset = node.test.left.col_offset)
            node.test.comparators[0] = ast.Name(id="@__FILE__")
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
################## Conditional Rewriters ##################
###########################################################

class ForLoopTargetRewriter(ast.NodeTransformer):
    """Rewrites loop target variables in case they are used 
    outside of the loops scope. This has to be executed after 
    the JuliaLoopScopeAnalysis transformer """
    def __init__(self) -> None:
        super().__init__()
        self._targets_out_of_scope = False
        self._target_vals: list[tuple] = []
    
    def visit_Module(self, node: ast.Module) -> Any:
        self._targets_out_of_scope = False
        self._target_vals = []
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
        self._targets_out_of_scope = target_state
        
        return node
    
    def visit_For(self, node: ast.For) -> Any:
        if self._targets_out_of_scope:
            # Get target and its default value
            target_id = get_id(node.target)
            target_default = self._get_default_val_from_iter(node)
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
                col_offset = node.col_offset,
                scopes = node.scopes)
            node.target.id = new_loop_id
            node.body.insert(0, new_var_assign)
        return node

    def _get_default_val_from_iter(self, node: ast.For):
        iter = node.iter
        if isinstance(iter, ast.Call) and get_id(iter.func) == "range":
            return ast.Constant(value = 0, scopes = iter.scopes)
        if id := get_id(iter):
            n = node.scopes.find[id]
            ann = node.annotation if hasattr(node, "annotation") else getattr(n, "annotation", None)
            if ann_id := get_id(ann):
                if ann_id == "int":
                    return ast.Constant(value = 0, scopes = iter.scopes)
                if ann_id == "float":
                    return ast.Constant(value = 0.0, scopes = iter.scopes)
                if ann_id.startswith("list") or ann_id.startswith("List"):
                    return ast.List(elts=[], ctx=ast.Load())
                if ann_id.startswith("Dict"):
                    return ast.Dict(keys=[], values = [], ctx=ast.Load())
                if ann_id.startswith("set"):
                    return ast.Call(
                        func = ast.Name(id='set', ctx=ast.Load()),
                        args = [],
                        keywords = [],
                        scopes = iter.scopes)
        return None


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
            annotation: str = get_ann_repr(arg.annotation) \
                if hasattr(arg, "annotation") else None
            # TODO: Optimize: "arg_id not in self._subscript_vals" (This is O(n^2))
            if not annotation or (annotation and not annotation.startswith("List"))\
                    or arg_id not in self._subscript_vals:
                continue
            arg_name = ast.Name(id=arg_id)
            val = self._build_offset_array_call(
                        arg_name, annotation, node.lineno, 
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
            func=ast.Name(id = "parent"),
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
                col_offset = 0
            )

            # Populate remaining fields
            copy_attributes(node, julia_module)

            return julia_module
        return node