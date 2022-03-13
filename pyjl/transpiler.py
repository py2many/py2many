from __future__ import annotations
import ast
from fileinput import lineno
from imp import init_frozen
from libcst import Yield

from numpy import isin
from py2many.exceptions import AstTypeNotSupported

import textwrap
import re

import pyjl.juliaAst as juliaAst

from .clike import CLikeTranspiler
from .plugins import (
    ATTR_DISPATCH_TABLE,
    DECORATOR_DISPATCH_TABLE,
    CONTAINER_DISPATCH_TABLE,
    FUNC_DISPATCH_TABLE,
    JULIA_INTEGER_TYPES,
    MODULE_DISPATCH_TABLE,
    DISPATCH_MAP,
    JULIA_NUM_TYPES,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.clike import _AUTO_INVOKED
from py2many.tracer import find_in_body, find_node_matching_name_and_type, \
    get_class_scope, is_class_type, is_enum

from typing import Any, Dict, List, Tuple, Union

_DEFAULT = "Any"


def get_decorator_id(decorator):
    id = get_id(decorator.func) if isinstance(
        decorator, ast.Call) else get_id(decorator)
    # TODO: Probably not correct
    if isinstance(id, list):
        id = id[0]
    return id if id is not None else decorator


def _parse_annotations(node_decorator_list: list):
    decorator_list_cpy = node_decorator_list.copy()
    decorator_list = list(map(get_decorator_id, decorator_list_cpy))

    if "dataclass" in decorator_list and "jl_dataclass" in decorator_list:
        decorator_list_cpy = filter(lambda e: get_decorator_id(
            e) != "dataclass", decorator_list_cpy)

    return decorator_list_cpy


class JuliaTranspiler(CLikeTranspiler):
    NAME = "julia"

    def __init__(self):
        super().__init__()
        self._headers = set([])
        self._default_type = _DEFAULT
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE

        # Added
        self._scope_stack: Dict[str, list] = {"loop": [], "func": []}
        self._nested_if_cnt = 0
        self._modules = []
        self._class_names = []

    def visit_Module(self, node) -> str:
        self._modules = list(path.name.split(
            ".")[0] for path in node.__files__)
        self._class_names = getattr(node, "class_names", [])
        return super().visit_Module(node)

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses

    def comment(self, text):
        return f"#= {text} \n=#"

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def visit_Constant(self, node: ast.Constant) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "nothing"
        elif isinstance(node.value, str):
            return self.visit_Str(node)
        elif isinstance(node.value, bytes):
            return self.visit_Bytes(node)
        elif isinstance(node.value, complex):
            str_value = str(node.value)
            return (
                str_value.replace("j", "im") if str_value.endswith(
                    "j") else str_value
            )
        else:
            return super().visit_Constant(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> str:
        typedecls = []

        # Parse function args       
        args_list = self._get_func_args(node)
        args = ", ".join(args_list)
        node.parsed_args = args_list

        # Visit decorators
        decorator_list = _parse_annotations(node.decorator_list)
        for decorator in decorator_list:
            d_id = get_decorator_id(decorator)
            if d_id in DECORATOR_DISPATCH_TABLE:
                ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if ret is not None:
                    return ret

        # Parse return type
        return_type = ""
        if not is_void_function(node):
            if node.returns:
                func_typename = (node.julia_annotation if hasattr(node, "julia_annotation")
                                 else self._typename_from_annotation(node, attr="returns"))
                return_type = f"::{super()._map_type(func_typename)}"

        template = ""
        if len(typedecls) > 0:
            template = "{{{0}}}".format(", ".join(typedecls))

        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""

        # Check if current function contains yield expressions
        annotation = ""
        py_yield = find_in_body(node.body, lambda x: isinstance(x, ast.Yield))
        if py_yield:
            annotation = "@resumable "
        
        funcdef = f"{annotation}function {node.name}{template}({args}){return_type}"

        is_python_main = getattr(node, "python_main", False)
        maybe_main = "\nmain()" if is_python_main else ""
        return f"{funcdef}\n{body}\nend\n{maybe_main}"

    def _get_func_args(self, node) -> list[str]:
        typenames, args = self.visit(node.args)
        args_list = []

        if len(typenames) and typenames[0] == None and hasattr(node, "self_type"):
            typenames[0] = node.self_type

        defaults = node.args.defaults
        len_defaults = len(defaults)
        len_args = len(args)
        for i in range(len_args):
            arg_typename = typenames[i]
            arg = args[i]
            if arg_typename != None and arg_typename != "T":
                arg_typename = super()._map_type(arg_typename)

            # Get default parameter values
            default = None
            if defaults:
                if len_defaults != len_args:
                    diff_len = len_args - len_defaults
                    default = defaults[i - diff_len] if i >= diff_len else None
                else:
                    default = defaults[i]

            if default is not None:
                default = self.visit(default)

            arg_signature = ""
            if arg_typename:
                arg_signature = f"{arg}::{arg_typename}" if default is None else f"{arg}::{arg_typename} = {default}"
            else:
                arg_signature = f"{arg}" if default is None else f"{arg} = {default}"
            args_list.append(arg_signature)
        
        return args_list

    def visit_Return(self, node) -> str:
        if node.value:
            return f"return {self.visit(node.value)}"
        return "return"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        # typename = "T"
        typename = ""
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Lambda(self, node) -> str:
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return "({0}) -> {1}".format(args_string, body)

    def visit_Attribute(self, node) -> str:
        attr = node.attr

        value_id = self.visit(node.value)

        if not value_id:
            value_id = ""

        if value_id == "sys":
            if attr == "argv":
                return "append!([PROGRAM_FILE], ARGS)"

        if is_enum(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_class_type(value_id, node.scopes):
            # return f"{value_id}::{attr}"
            if find_node_matching_name_and_type(attr, ast.FunctionDef, node.scopes):
                return f"{attr}({value_id})"

        return f"{value_id}.{attr}"

    def visit_Call(self, node: ast.Call) -> str:
        fname = self.visit(node.func)
        vargs = []
        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret

        # Check if first arg is of class type.
        # If it is, search for the function in the class scope
        fndef = node.scopes.find(fname)
        if vargs and (class_scope := get_class_scope(vargs[0], node.scopes)):
            fndef = class_scope.scopes.find(fname)

        if fndef and hasattr(fndef, "args"):
            converted = []
            for varg, fnarg, node_arg in zip(vargs, fndef.args.args, node.args):
                actual_type = self._typename_from_annotation(node_arg)
                declared_type = self._typename_from_annotation(
                    fnarg)  # if fnarg.arg != "self" else None
                if declared_type != None and declared_type != self._default_type \
                        and actual_type != self._default_type and actual_type != declared_type:
                    converted.append(f"convert({declared_type}, {varg})")
                else:
                    converted.append(varg)
        else:
            converted = vargs

        args = ", ".join(converted)
        return f"{fname}({args})"

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []

        # Replace square brackets for normal brackets in lhs
        target = target.replace("[", "(").replace("]", ")")

        # Add variables to current scope vars
        target_vars = list(filter(None, re.split(r"\(|\)|\,|\s", target)))
        self._scope_stack["loop"].extend(target_vars)

        buf.append(f"for {target} in {it}")
        buf.extend([self.visit(c) for c in node.body])
        buf.append("end")

        # Remove all items when leaving the scope
        start = len(self._scope_stack["loop"]) - len(target_vars)
        end = len(self._scope_stack["loop"])
        del self._scope_stack["loop"][len(target_vars) - start:end]

        return "\n".join(buf)

    def visit_Str(self, node: ast.Str) -> str:
        node_str = node.value
        # Escape special characters
        node_str = node_str.translate(str.maketrans({"\a": "\\a", "\b": "\\b",
                                                     "\f": "\\f", "\n": "\\n", "\r": "\\r", "\v": "\\v", "\t": "\\t",
                                                     '"': '\\"'}))
        return f'"{node_str}"'

    def visit_Bytes(self, node: ast.Bytes) -> str:
        bytes_str: str = str(node.s)
        # Replace ['] by ["]
        bytes_str = f"{bytes_str[0]}\"{bytes_str[2:-1]}\""
        # Decoding does not give representative value
        # return 'b"' + bytes_str.decode("ascii", "backslashreplace") + '"'
        return f"{bytes_str}"

    def visit_Compare(self, node) -> str:
        left = self.visit(node.left)
        comparators = node.comparators
        ops = node.ops

        comp_exp = ""
        for i in range(len(node.comparators)):
            comparator = comparators[i]
            op = ops[i]
            comp_str = self.visit(comparator)
            op_str = self.visit(op)

            if isinstance(op, ast.In) or isinstance(op, ast.NotIn):
                if hasattr(comparator, "annotation"):
                    self._generic_typename_from_annotation(node.comparators[0])
                    value_type = getattr(
                        comparator.annotation, "generic_container_type", None
                    )
                    if value_type and value_type[0] == "Dict":
                        comp_str = f"keys({comp_str})"

            if (isinstance(op, ast.Eq)
                    and (is_mutable(node.scopes, comp_str) or comp_str == "nothing")):
                op_str = "==="

            # Isolate composite operations
            if isinstance(comparator, ast.BinOp) or isinstance(comparator, ast.BoolOp):
                comp_str = f"({comp_str})"

            comp_exp += f" {op_str} {comp_str}"

        # Isolate composite operations
        if isinstance(node.left, ast.BinOp) or isinstance(node.left, ast.BoolOp):
            left = f"({left})"

        return f"{left}{comp_exp}"

    def visit_Name(self, node) -> str:
        if get_id(node) == "None":
            return "nothing"
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "nothing"
        else:
            return super().visit_NameConstant(node)

    def visit_If(self, node: ast.If) -> str:
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        buf = []
        cond = "if" if self._nested_if_cnt == 0 else "elseif"
        buf.append(f"{cond} {self.visit(node.test)}")
        buf.extend([self.visit(child) for child in node.body])

        orelse = node.orelse

        if len(orelse) == 1 and isinstance(orelse[0], ast.If):
            self._nested_if_cnt += 1
            buf.append(self.visit(orelse[0]))
            self._nested_if_cnt -= 1
        else:
            if len(orelse) >= 1:
                buf.append("else")
                orelse = [self.visit(child) for child in node.orelse]
                orelse = "\n".join(orelse)
                buf.append(orelse)

        if self._nested_if_cnt == 0:
            buf.append("end")

        return "\n".join(buf)

    def visit_While(self, node) -> str:
        buf = []
        buf.append(f"while {self.visit(node.test)}")
        buf.extend([self.visit(n) for n in node.body])
        buf.append("end")
        return "\n".join(buf)

    def visit_BinOp(self, node) -> str:
        left_jl_ann = node.left.julia_annotation
        right_jl_ann = node.right.julia_annotation

        # Visit left and right
        left = self.visit_List(node.left) if isinstance(
            node.left, ast.List) else self.visit(node.left)
        right = self.visit_List(node.right) if isinstance(
            node.right, ast.List) else self.visit(node.right)

        if isinstance(node.op, ast.Mult):
            # Cover multiplication between List and Number
            if((isinstance(node.right, ast.Num) or (right_jl_ann in JULIA_NUM_TYPES)) and
                    ((isinstance(node.left, ast.List) or left_jl_ann == "Array" or left_jl_ann == "Vector") or
                     (isinstance(node.left, ast.Str) or left_jl_ann == "String"))):
                return f"repeat({left},{right})"

            if((isinstance(node.left, ast.Num) or (left_jl_ann in JULIA_NUM_TYPES)) and
                    ((isinstance(node.right, ast.List) or right_jl_ann == "Array" or right_jl_ann == "Vector") or
                     (isinstance(node.right, ast.Str) or right_jl_ann == "String"))):
                return f"repeat({right},{left})"

            # Cover Python Int and Boolean multiplication (also supported in Julia)
            if (((isinstance(node.right, ast.Num) or right_jl_ann in JULIA_NUM_TYPES)
                    and (isinstance(node.left, ast.BoolOp) or left_jl_ann == "Bool")) or
                    ((isinstance(node.left, ast.Num) or left_jl_ann in JULIA_NUM_TYPES)
                     and (isinstance(node.right, ast.BoolOp) or right_jl_ann == "Bool"))):
                return f"{left}*{right}"

        if isinstance(node.op, ast.Add):
            # Cover Python list addition
            if ((isinstance(node.right, ast.List) and isinstance(node.left, ast.List))
                    or ((right_jl_ann == "Array" or right_jl_ann == "Vector")
                        and (left_jl_ann == "Array" or left_jl_ann == "Vector"))):
                return f"[{left};{right}]"

            # Cover Python String concatenation
            if ((isinstance(node.right, ast.Str) and isinstance(node.left, ast.Str))
                    or (right_jl_ann == "String" and left_jl_ann == "String")):
                return f"{left} * {right}"

        # By default, call super
        return super().visit_BinOp(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        if isinstance(node.operand, (ast.Call, ast.Num)):
            # Shortcut if parenthesis are not needed
            return f"{self.visit(node.op)}{self.visit(node.operand)}"
        return super().visit_UnaryOp(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> str:
        # Get class declarations and assignments
        self._visit_class_fields(node)

        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        # Visit decorators
        decorator_list = _parse_annotations(node.decorator_list)
        for decorator in decorator_list:
            if (d_id := get_decorator_id(decorator)) in DECORATOR_DISPATCH_TABLE:
                dec_ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if dec_ret:
                    return dec_ret

        # TODO: Investigate Julia traits
        struct_name = get_id(node)
        bases = [self.visit(base) for base in node.bases]
        struct_def = f"mutable struct {struct_name} <: {bases[0]}" \
            if bases else f"mutable struct {struct_name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(self.visit(b))
        body = "\n".join(body)

        if hasattr(node, "constructors"):
            return f"{struct_def}\n{node.fields}\n{node.constructors}\nend\n{body}"

        return f"{struct_def}\n{node.fields}\nend\n{body}"

    def _visit_class_fields(self, node):
        extractor = DeclarationExtractor(JuliaTranspiler())
        extractor.visit(node)
        node.declarations = extractor.get_declarations()
        node.declarations_with_defaults = extractor.get_declarations_with_defaults()
        node.class_assignments = extractor.class_assignments

        declarations: dict[str, (str, Any, Any)] = node.declarations_with_defaults

        decs = []
        fields = []
        fields_with_defaults = []
        for declaration, (typename, default, parent) in declarations.items():
            dec = declaration.split(".")
            if dec[0] == "self":
                declaration = dec[1]
            if self._class_names is not None and typename in self._class_names:
                typename = f"Abstract{typename}"

            decs.append(declaration)

            field = declaration \
                if typename == "" else f"{declaration}::{typename}"
            fields.append(field)
            
            # Default field values
            if (default and isinstance(parent, ast.ClassDef)) or \
                    (isinstance(parent, ast.FunctionDef) and parent.name == "__init__"):
                if declaration != (default_value:= self.visit(default)):
                    fields_with_defaults.append((declaration, field, default_value))

        if fields_with_defaults:
            decs_str = ", ".join(decs)
            default_decs = []
            default_fields = []
            for (declaration, field, default_value) in fields_with_defaults:
                default_decs.append(declaration)
                default_fields.append(f"{field} = {default_value}")
            default_decs = ", ".join(default_decs)
            default_fields = ", ".join(default_fields)

            # Define constructor with defaults and default constructor
            node.constructors = f"""
                {node.name}({default_fields}) =
                    new({default_decs})
                {node.name}({decs_str}) =
                    new({decs_str})"""

        node.fields = "" if fields == [] else "\n".join(fields)

    def visit_StrEnum(self, node) -> str:
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == _AUTO_INVOKED:
                var = f'"{member}"'
            fields.append((member, var))
        return self._visit_enum(node, "String", fields)

    def visit_IntEnum(self, node) -> str:
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == _AUTO_INVOKED:
                var = i
            fields.append((member, var))
        return self._visit_enum(node, "Int64", fields)

    def _visit_enum(self, node, typename: str, fields: List[Tuple]) -> str:
        decorators = [get_decorator_id(d) for d in node.decorator_list]
        field_str = ""
        for field, value in fields:
            field_str += f"\t{field}\n"
        if("unique" in decorators and typename not in JULIA_INTEGER_TYPES):
            return textwrap.dedent(
                f"@enum {node.name}::{typename} begin\n{field_str}end"
            )
        else:
            # Cover case in pyenum where values are unique and strings
            self._usings.add("PyEnum")
            return textwrap.dedent(
                f"@pyenum {node.name}::{typename} begin\n{field_str}end"
            )

    def visit_IntFlag(self, node) -> str:
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == _AUTO_INVOKED:
                var = 1 << i
            fields.append((member, var))
        return self._visit_enum(node, "Int64", fields)

    def _import(self, name: str) -> str:
        return f"import {name}"  # import or using?

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if module_name in self._modules:
            return f"include(\"{module_name}.jl\")"

        jl_module_name = module_name
        imports = []
        for name in names:
            lookup = f"{module_name}.{name}"
            if lookup in MODULE_DISPATCH_TABLE:
                jl_module_name, jl_name = MODULE_DISPATCH_TABLE[lookup]
                imports.append(jl_name)
            else:
                imports.append(name)
        str_imports = ", ".join(imports)
        return f"using {jl_module_name}: {str_imports}"

    def visit_List(self, node) -> str:
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return (
            f"({elements_str})"
            if hasattr(node, "lhs") and node.lhs
            else f"[{elements_str}]"
        )

    def visit_Set(self, node) -> str:
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"Set([{elements_str}])"

    def visit_Dict(self, node) -> str:
        kv_pairs = []
        for key, value in zip (node.keys, node.values):
            if key:
                kv_pairs.append(f"{self.visit(key)} => {self.visit(value)}")
            else:
                if isinstance(value, ast.Dict):
                    kv_pairs.append(f"{self.visit(value)}...")
        
        kv_pairs = ", ".join(kv_pairs)
        return f"Dict({kv_pairs})"

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if index == None:
            return "{0}[(Something, Strange)]".format(value)
        if hasattr(node, "is_annotation"):
            if value in CONTAINER_DISPATCH_TABLE:
                value = CONTAINER_DISPATCH_TABLE[value]
            if value == "Tuple":
                return "({0})".format(index)
            return "{0}{{{1}}}".format(value, index)

        # Julia array indices start at 1; Change "-1" for "end"
        if isinstance(index, str) and index.lstrip("-").isnumeric():
            return f"{value}[{int(index)+1}]" if index != "-1" else f"{value}[end]"
        elif isinstance(index, int) or isinstance(index, float):
            return f"{value}[{index + 1}]"

        # TODO: Optimize; value_type is computed once per definition
        self._generic_typename_from_annotation(node.value)
        if hasattr(node.value, "annotation"):
            value_type = getattr(node.value.annotation,
                                 "generic_container_type", None)
            if (value_type is not None and value_type[0] == "List"
                    and not isinstance(node.slice, ast.Slice)):
                # Julia array indices start at 1
                return f"{value}[{index} + 1]"

        # Increment index's that use for loop variables
        split_index = set(
            filter(None, re.split(r"\(|\)|\[|\]|-|\s|\:", index)))
        intsct = split_index.intersection(self._scope_stack["loop"])
        if intsct and not isinstance(node.slice, ast.Slice):
            return f"{value}[{index} + 1]"

        return f"{value}[{index}]"

    def visit_Index(self, node) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node) -> str:
        lower = "begin"
        if node.lower:
            lower = self.visit(node.lower)
        upper = "end"
        if node.upper:
            upper = self.visit(node.upper)

        # Julia array indices start at 1
        if lower == -1 or lower.startswith("-"):
            lower = "end"
            return f"{lower}:{lower}"
        elif isinstance(lower, ast.Num) or (isinstance(lower, str) and lower.isnumeric()):
            lower = f"{(int(lower) + 1)}"
        elif lower != "begin":
            lower = f"({lower} + 1)"

        return f"{lower}:{upper}"

    def visit_Ellipsis(self, node: ast.Ellipsis) -> str:
        return "..."

    def visit_Tuple(self, node) -> str:
        elts = [self.visit(e) for e in node.elts]
        elts = ", ".join(elts)
        if hasattr(node, "is_annotation"):
            return elts
        return "({0})".format(elts)

    def visit_Try(self, node, finallybody=None) -> str:
        buf = []
        buf.append("try")
        buf.extend([self.visit(child) for child in node.body])
        if len(node.handlers) > 0:
            buf.append("catch exn")
            for handler in node.handlers:
                buf.append(self.visit(handler))
        if node.finalbody:
            buf.append("finally")
            buf.extend([self.visit(child) for child in node.finalbody])
        buf.append("end")
        return "\n".join(buf)

    def visit_ExceptHandler(self, node) -> str:
        buf = []
        name = "exn"
        if node.name:
            buf.append(f" let {node.name} = {name}")
            name = node.name
        if node.type:
            type_str = self.visit(node.type)
            buf.append(f"if {name} isa {type_str}")
        buf.extend([self.visit(child) for child in node.body])
        if node.type:
            buf.append("end")
        if node.name:
            buf.append("end")
        return "\n".join(buf)

    def visit_Assert(self, node) -> str:
        return "@assert({0})".format(self.visit(node.test))

    def visit_AnnAssign(self, node: ast.AnnAssign) -> str:
        target = self.visit(node.target)
        type_str = self.visit(node.annotation)
        val = None
        if node.value is not None:
            val = self.visit(node.value)
        # If there is a Julia annotation, get that instead of the
        # default Python annotation
        type_str = (
            node.julia_annotation
            if (node.julia_annotation and node.julia_annotation != "nothing")
            else type_str
        )

        if val:
            if not type_str or type_str == self._default_type:
                return f"{target} = {val}"
            return f"{target}::{type_str} = {val}"
        else:
            if not type_str or type_str == self._default_type:
                return f"{target}"
            return f"{target}::{type_str}"

    def visit_AugAssign(self, node: ast.AugAssign) -> str:
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2}".format(target, op, val)

    def _visit_AssignOne(self, node: ast.Assign, target) -> str:
        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            return "{0} = {1}".format(", ".join(elts), value)

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return "{0} = {1}".format(target_id, value)

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            if value == None:
                value = "nothing"
            return "{0} = {1}".format(target, value)

        # TODO: Check this
        # definition = node.scopes.parent_scopes.find(get_id(target))
        # if definition is None:
        #     definition = node.scopes.find(get_id(target))

        # Visit target and value
        target_str = self.visit(target)
        value = self.visit(node.value)

        # Custom type comments to preserve literal values
        if value is not None and value.isdigit():
            value = int(value)
            if type_c := getattr(node, "type_comment", None):
                if type_c == "BLiteral":
                    value = bin(value)
                if type_c == "OLiteral":
                    value = oct(value)
                if type_c == "HLiteral":
                    value = hex(value)

        expr = f"{target_str} = {value}"
        # if isinstance(target, ast.Name) and defined_before(definition, node):
        #     f"{expr};"
        return expr

    def visit_Delete(self, node) -> str:
        target = node.targets[0]
        target_name = self.visit(target)
        node_assign = (
            find_node_matching_name_and_type(target_name,
                                             (ast.Assign, ast.AnnAssign, ast.AugAssign), node.scopes)[0]
            if not hasattr(target, "annotation") else target
        )
        if node_assign and hasattr(node_assign, "annotation"):
            type_ann = self._typename_from_annotation(node_assign)
            if isinstance(type_ann, ast.List) or re.match(r"Vector{\S*}", type_ann):
                return f"empty!({target_name})"

        raise AstTypeNotSupported(
            f"{target_name} does not support del"
        )

    def visit_Raise(self, node) -> str:
        if node.exc is not None:
            return "throw({0})".format(self.visit(node.exc))
        # This handles the case where `raise` is used without
        # specifying the exception.
        return "error()"

    def visit_Await(self, node) -> str:
        return f"wait({self.visit(node.value)})"

    def visit_AsyncFunctionDef(self, node:ast.AsyncFunctionDef) -> str:
        # Parse function args       
        args_list = self._get_func_args(node)
        args = ", ".join(args_list)

        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)

        if hasattr(node, "returns") and node.returns:
            f"@async function {node.name} ({args})::{self.visit(node.returns)}\n{body}end"

        return f"@async function {node.name}({args})\n{body}\nend"

    def visit_Yield(self, node: ast.Yield) -> str:
        if "ResumableFunctions" not in self._usings:
            self._usings.add("ResumableFunctions")
        if node.value:
            return f"@yield {self.visit(node.value)}"
        else:
            return "@yield"

    def visit_YieldFrom(self, node: ast.YieldFrom) -> str:
        # Currently not supported
        return f"@yield from {self.visit(node.value)}"

    def visit_Print(self, node) -> str:
        buf = []
        for n in node.values:
            value = self.visit(n)
            buf.append('println("{{:?}}",{0})'.format(value))
        return "\n".join(buf)

    def visit_GeneratorExp(self, node) -> str:
        elt = self.visit(node.elt)
        generators = node.generators
        gen_expr = self._visit_generators(generators)
        return f"({elt} {gen_expr})"

    def visit_ListComp(self, node) -> str:
        elt = self.visit(node.elt)
        generators = node.generators
        list_comp = self._visit_generators(generators)
        return f"[{elt} {list_comp}]"

    def visit_DictComp(self, node: ast.DictComp) -> str:
        key = self.visit(node.key)
        value = self.visit(node.value)
        generators = node.generators
        dict_comp = (f"{key} => {value} " +
                     self._visit_generators(generators))

        return f"Dict({dict_comp})"

    def _visit_generators(self, generators):
        gen_exp = []
        for i in range(len(generators)):
            generator = generators[i]
            target = self.visit(generator.target)
            iter = self.visit(generator.iter)
            exp = f"for {target} in {iter}"
            gen_exp.append(exp) \
                if i == 0 \
                else gen_exp.append(f" {exp}")
            filter_str = ""
            if(len(generator.ifs) == 1):
                filter_str += f" if {self.visit(generator.ifs[0])} "
            else:
                for i in range(0, len(generator.ifs)):
                    gen_if = generator.ifs[i]
                    filter_str += f" if {self.visit(gen_if)}" if i == 0 else f" && {self.visit(gen_if)} "
            gen_exp.append(filter_str)

        return "".join(gen_exp)

    def visit_Global(self, node) -> str:
        return "global {0}".format(", ".join(node.names))

    def visit_Starred(self, node) -> str:
        return f"{self.visit(node.value)}..."

    def visit_IfExp(self, node) -> str:
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"{test} ? ({body}) : ({orelse})"

    def visit_JoinedStr(self, node: ast.JoinedStr) -> Any:
        str_repr = ""
        for value in node.values:
            if isinstance(value, ast.FormattedValue):
                str_repr += f"$({self.visit(value)})"
            else:
                tmp_val: str = self.visit(value).replace("\"", "")
                str_repr += tmp_val
        return f"\"{str_repr}\""

    def visit_FormattedValue(self, node: ast.FormattedValue) -> Any:
        value = self.visit(node.value)
        conversion = node.conversion
        if conversion == 115:
            value = str(value)
        elif conversion == 114:
            value = repr(value)
        elif conversion == 94:
            value = ascii(value)

        if f_spec_val := getattr(node, "format_spec", None):
            f_spec_val: str = self.visit(f_spec_val)
            # Supporting rounding
            if re.match(r".[\d]*", f_spec_val):
                f_spec_parsed = f_spec_val.split(".")[1].replace("\"", "")
                return f"round({value}, digits={f_spec_parsed})"

        return f"{value}"

    def visit_With(self, node: ast.With) -> Any:
        items = [self.visit(it) for it in node.items]
        items = "; ".join(items)
        body = [self.visit(n) for n in node.body]
        body = "\n".join(body)
        return f"{items} \n{body}\nend"
    
    def visit_withitem(self, node: ast.withitem) -> Any:
        cntx_data = self.visit(node.context_expr)
        if hasattr(node, "optional_vars") and node.optional_vars:
            optional = self.visit(node.optional_vars)
            return f"{cntx_data} do {optional}"
        return f"{cntx_data} do"

    ######################################################
    #################### Julia Nodes #####################
    ######################################################

    def visit_AbstractType(self, node: juliaAst.AbstractType) -> Any:
        name = self.visit(node.value)
        extends = None
        if node.extends is not None:
            extends = self.visit(node.extends)
        return (f"abstract type Abstract{name} end"
                if extends is None
                else f"abstract type Abstract{name} <: {extends} end")
