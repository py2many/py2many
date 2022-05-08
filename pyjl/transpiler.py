from enum import IntFlag
import ast

import textwrap
import re
from py2many.exceptions import AstUnsupportedOperation
from pyjl.global_vars import RESUMABLE

import pyjl.juliaAst as juliaAst

from .clike import JULIA_INTEGER_TYPES, JULIA_NUM_TYPES, CLikeTranspiler
from .plugins import (
    ATTR_DISPATCH_TABLE,
    DECORATOR_DISPATCH_TABLE,
    FUNC_DISPATCH_TABLE,
    MODULE_DISPATCH_TABLE,
    DISPATCH_MAP,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.clike import _AUTO_INVOKED
from py2many.tracer import find_closest_scope, \
    get_class_scope, is_class_or_module, is_class_type

from typing import Any, List

SPECIAL_CHARACTER_MAP = {
    "\a": "\\a", 
    "\b": "\\b",
    "\f": "\\f", 
    "\r": "\\r", 
    "\v": "\\v", 
    "\t": "\\t",
    "\xe9":"\\xe9",
}

# For now just includes SPECIAL_CHARACTER_MAP
DOCSTRING_TRANSLATION_MAP = SPECIAL_CHARACTER_MAP | {} 

STR_SPECIAL_CHARACTER_MAP = SPECIAL_CHARACTER_MAP | {
    "\"": "\\\"",
    "\'": "\\\'",
    "\\": "\\\\",
    "$": "\\$",
    "\n": "\\n"
}

BYTES_SPECIAL_CHARACTER_MAP = SPECIAL_CHARACTER_MAP | {
    "\"": "\\\"",
    "\n": "\\n"
}

class JuliaTranspiler(CLikeTranspiler):
    NAME = "julia"

    SPECIAL_METHOD_TABLE = {
        ast.Add: "__add__",
        ast.Sub: "__sub__",
        ast.Mult: "__mul__",
        ast.Div: "__div__",
        ast.MatMult: "__matmul__",
        ast.Div: "__div__",
        ast.RShift: "__rshift__",
        ast.LShift: "__lshift__",
        ast.Mod: "__mod__",
        ast.FloorDiv: "__floordiv__",
        ast.BitOr: "__or__",
        ast.BitAnd: "__and__",
        ast.BitXor: "__xor__",
        ast.Pow: "__pow__"
    }

    def __init__(self):
        super().__init__()
        self._headers = set([])
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE

        # Added
        self._julia_num_types = JULIA_NUM_TYPES
        self._julia_integer_types = JULIA_INTEGER_TYPES
        self._str_special_character_map = STR_SPECIAL_CHARACTER_MAP
        self._bytes_special_character_map = BYTES_SPECIAL_CHARACTER_MAP
        self._docstr_special_character_map = DOCSTRING_TRANSLATION_MAP
        self._special_method_table = self.SPECIAL_METHOD_TABLE    

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses

    def globals(self):
        return "\n".join(self._globals)

    def comment(self, text: str) -> str:
        return f"#= {text} =#"

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def visit_Constant(self, node: ast.Constant, is_comment_str = False) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return self._none_type
        elif isinstance(node.value, str):
            return self.visit_Str(node, is_comment_str)
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

    def visit_Str(self, node: ast.Str, is_comment_str = False) -> str:
        # Escape special characters
        trs_map = str.maketrans(self._str_special_character_map) \
            if not is_comment_str \
            else self._docstr_special_character_map
        node_str = node.value.translate(str.maketrans(trs_map))
        return f'"{node_str}"' if not is_comment_str else node_str

    def visit_Bytes(self, node: ast.Bytes) -> str:
        bytes_str: str = str(node.s)
        byte_name = bytes_str[0]
        content = bytes_str[2:-1]
        bytes_str = content.translate(str.maketrans(self._bytes_special_character_map))
        # Decoding does not give representative value
        # return 'b"' + bytes_str.decode("ascii", "backslashreplace") + '"'
        return f"{byte_name}\"{bytes_str}\""

    def visit_FunctionDef(self, node: ast.FunctionDef) -> str:
        typedecls = []

        # Parse function args       
        args_list = self._get_args(node)
        args = ", ".join(args_list)
        node.parsed_args = args

        # Parse return type
        return_type = ""
        if not is_void_function(node):
            if node.returns:
                func_typename = self._typename_from_annotation(node, attr="returns")
                return_type = f"::{self._map_type(func_typename)}"
        node.return_type = return_type

        template = ""
        if len(typedecls) > 0:
            template = "{{{0}}}".format(", ".join(typedecls))
        node.template = template

        # Visit function body
        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        body = "\n".join(body)
        if body == "...":
            body = ""

        node.is_python_main = is_python_main = getattr(node, "python_main", False)

        # Visit decorators
        for ((d_id, _), decorator) in zip(node.parsed_decorators.items(), node.decorator_list):
            if d_id in DECORATOR_DISPATCH_TABLE:
                ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if ret is not None:
                    return ret
        
        funcdef = f"function {node.name}{template}({args}){return_type}"

        is_python_main = getattr(node, "python_main", False)
        maybe_main = "\nmain()" if is_python_main else ""
        return f"{funcdef}\n{body}\nend\n{maybe_main}"

    def _get_args(self, node, is_constructor = False) -> list[str]:
        typenames, args = self.visit(node.args)
        args_list = []

        if not is_constructor:
            if len(typenames) and typenames[0] == None and hasattr(node, "self_type"):
                typenames[0] = node.self_type

        defaults = node.args.defaults
        len_defaults = len(defaults)
        len_args = len(args)
        for i in range(len_args):
            arg = args[i]
            arg_typename = typenames[i]
            if arg_typename == self._default_type:
                arg_typename = None

            if arg_typename and arg_typename != "T":
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

    def visit_Lambda(self, node) -> str:
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return f"({args_string}) -> {body}"

    def visit_Attribute(self, node) -> str:
        attr = node.attr
        value_id = self.visit(node.value)

        if not value_id:
            value_id = ""

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
                declared_type = self._typename_from_annotation(fnarg)
                if declared_type and actual_type and declared_type != self._default_type \
                        and actual_type != self._default_type and actual_type != declared_type and \
                        not getattr(actual_type, "container_type", None): # TODO: Container types are source of conflict
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
        buf.append(f"for {target} in {it}")
        buf.extend([self.visit(c) for c in node.body])
        buf.append("end")

        return "\n".join(buf)

    def visit_Compare(self, node) -> str:
        left = self.visit(node.left)
        comparators = node.comparators
        ops = node.ops

        comp_exp = []
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

            if ((isinstance(op, ast.Eq) or isinstance(op, ast.Is))
                    and (is_mutable(node.scopes, comp_str) or comp_str == self._none_type)):
                op_str = "==="

            # Isolate composite operations
            if isinstance(comparator, ast.BinOp) or isinstance(comparator, ast.BoolOp):
                comp_str = f"({comp_str})"

            comp_exp.append(f"{op_str} {comp_str}")

        # Isolate composite operations
        if isinstance(node.left, ast.BinOp) or isinstance(node.left, ast.BoolOp):
            left = f"({left})"

        comp_exp = " ".join(comp_exp)
        return f"{left} {comp_exp}"

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return self._none_type
        else:
            return super().visit_NameConstant(node)

    def visit_If(self, node: ast.If) -> str:
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        buf = []
        cond = "if" if not getattr(node, "is_orelse", None) else "elseif"
        buf.append(f"{cond} {self.visit(node.test)}")
        buf.extend([self.visit(child) for child in node.body])

        orelse = node.orelse
        if len(orelse) == 1 and isinstance(orelse[0], ast.If):
            orelse[0].is_orelse = True
            buf.append(self.visit(orelse[0]))
        else:
            if len(orelse) >= 1:
                buf.append("else")
                orelse = [self.visit(child) for child in node.orelse]
                orelse = "\n".join(orelse)
                buf.append(orelse)

        if not getattr(node, "is_orelse", None):
            buf.append("end")

        return "\n".join(buf)

    def visit_While(self, node) -> str:
        buf = []
        buf.append(f"while {self.visit(node.test)}")
        buf.extend([self.visit(n) for n in node.body])
        buf.append("end")
        return "\n".join(buf)

    def visit_BinOp(self, node: ast.BinOp) -> str:
        left_jl_ann: str = self._typename_from_type_node(node.left.annotation, 
            default=self._default_type)
        right_jl_ann: str = self._typename_from_type_node(node.right.annotation, 
            default=self._default_type)

        is_list = lambda x: x.startswith("Array") or x.startswith("Vector")
        is_tuple = lambda x: x.startswith("Tuple")

        # Visit left and right
        left = self.visit(node.left)
        right = self.visit(node.right)

        if is_class_type(left, node.scopes) or \
                is_class_type(right, node.scopes):
            op_type = type(node.op)
            if op_type in self._special_method_table:
                new_op: str = self._special_method_table[op_type]
                return f"{new_op}({left}, {right})"

        if isinstance(node.op, ast.Mult):
            # Cover multiplication between List/Tuple and Int
            if isinstance(node.right, ast.Num) or right_jl_ann.startswith("Int"):
                if ((isinstance(node.left, ast.List) or is_list(left_jl_ann))  or
                        (isinstance(node.left, ast.Str) or left_jl_ann == "String")):
                    return f"repeat({left},{right})"
                elif isinstance(node.left, ast.Tuple) or is_tuple(left_jl_ann):
                    return f"repeat([{left}...],{right})"

            if isinstance(node.left, ast.Num) or left_jl_ann.startswith("Int"):
                if ((isinstance(node.right, ast.List) or is_list(right_jl_ann)) or
                        (isinstance(node.right, ast.Str) or right_jl_ann == "String")):
                    return f"repeat({right},{left})"
                elif isinstance(node.right, ast.Tuple) or is_tuple(right_jl_ann):
                    return f"repeat([{right}...],{left})"

            # Cover Python Int and Boolean multiplication (also supported in Julia)
            if (((isinstance(node.right, ast.Num) or right_jl_ann in self._julia_num_types)
                    and (isinstance(node.left, ast.BoolOp) or left_jl_ann == "Bool")) or
                    ((isinstance(node.left, ast.Num) or left_jl_ann in self._julia_num_types)
                     and (isinstance(node.right, ast.BoolOp) or right_jl_ann == "Bool"))):
                return f"{left}*{right}"

        if isinstance(node.op, ast.Add):
            # Add two lists
            if ((isinstance(node.right, ast.List) and isinstance(node.left, ast.List))
                    or (is_list(right_jl_ann) and is_list(left_jl_ann))):
                return f"append!({left}, {right})"

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
        for ((d_id, _), decorator) in zip(node.parsed_decorators.items(), node.decorator_list):
            if d_id in DECORATOR_DISPATCH_TABLE:
                dec_ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if dec_ret:
                    return dec_ret

        # TODO: Investigate Julia traits
        struct_name = get_id(node)
        bases = []
        for base in node.jl_bases:
            bases.append(self.visit(base))

        struct_def = f"mutable struct {struct_name} <: {bases[0]}" \
            if bases else f"mutable struct {struct_name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(self.visit(b))
        body = "\n".join(body)

        docstring = self._get_docstring(node)
        maybe_docstring = f"{docstring}\n" if docstring else ""
        maybe_constructor = f"\n{node.constructor_str}" if hasattr(node, "constructor_str") else ""

        return f"{struct_def}\n{maybe_docstring}{node.fields_str}{maybe_constructor}\nend\n{body}"

    def _visit_class_fields(self, node):
        extractor = DeclarationExtractor(JuliaTranspiler())
        extractor.visit(node)
        node.declarations = extractor.get_declarations()
        node.declarations_with_defaults = extractor.get_declarations_with_defaults()
        node.class_assignments = extractor.class_assignments
        
        declarations: dict[str, (str, Any)] = node.declarations_with_defaults
        has_defaults = any(list(map(lambda x: x[1][1] is not None, declarations.items())))

        # Reorganize fields, so that defaults are last
        dec_items = sorted(declarations.items(), key = lambda x: (x[1][1] != None, x), reverse=False) \
            if has_defaults \
            else declarations.items()

        decs = []
        fields = []
        fields_str = []
        for declaration, (typename, default) in dec_items:
            dec = declaration.split(".")
            if dec[0] == "self":
                declaration = dec[1]
            if is_class_or_module(typename, node.scopes):
                typename = f"Abstract{typename}"

            decs.append(declaration)
            fields_str.append(declaration if not typename else f"{declaration}::{typename}")
            
            # Default field values
            fields.append((declaration, typename, default))

        if not hasattr(node, "constructor"):
            if has_defaults:
                decs_str = ", ".join(decs)
                default_fields = []
                for (declaration, typename, default) in fields:
                    field = []
                    if typename:
                        field.append(f"{declaration}::{typename}")
                    else:
                        field.append(declaration)

                    if default:
                        default_value = self.visit(default)
                        field.append(f" = {default_value}")
                    field = "".join(field)
                    default_fields.append(field)
                default_fields = ", ".join(default_fields)

                # Define constructor with defaults and default constructor
                node.constructor_str = f"""
                    {node.name}({default_fields}) =
                        new({decs_str})"""
        else:
            # Case where __init__ has custom implementation
            args: ast.arguments= node.constructor.args
            arg_ids = [arg.arg for arg in args.args]
            for (declaration, typename, default) in fields:
                if default and declaration not in arg_ids:
                    args.args.append(ast.arg(
                        arg = declaration,
                        annotation = ast.Name(id=typename),
                    ))
                    args.defaults.append(default)
            node.constructor_str = self.visit(node.constructor)


        node.fields = fields
        node.fields_str = "\n".join(fields_str)

    def visit_StrEnum(self, node) -> str:
        return self._visit_enum(node, "String", str)

    def visit_IntEnum(self, node) -> str:
        return self._visit_enum(node, "Int64", int)

    def visit_IntFlag(self, node: IntFlag) -> str:
        return self._visit_enum(node, "Int64", IntFlag)

    def _visit_enum(self, node, typename: str, caller_type) -> str:
        extractor = DeclarationExtractor(JuliaTranspiler())
        extractor.visit(node)
        node.declarations_with_defaults = extractor.get_declarations_with_defaults()
        declarations: dict[str, (str, Any)] = node.declarations_with_defaults

        fields = []
        for i, (declaration, (t_name, default)) in enumerate(declarations.items()):
            val = self.visit(default)
            if val == _AUTO_INVOKED:
                if caller_type == IntFlag:
                    val = 1 << i
                elif caller_type == int:
                    val = i
                elif caller_type == str:
                    val = f'"{default}"'
            fields.append(f"{declaration} = {val}")
        field_str = "\n".join(fields)

        if("unique" in node.parsed_decorators or typename not in self._julia_integer_types):
            return textwrap.dedent(
                f"@enum {node.name}::{typename} begin\n{field_str}end"
            )
        else:
            # Cover case where values are not unique and not strings
            self._usings.add("PyEnum")
            return textwrap.dedent(
                f"@pyenum {node.name}::{typename} begin\n{field_str}end"
            )

    def _import(self, name: str) -> str:
        if name in self._modules:
            return f"include(\"{name}.jl\")"
        return f"import {name}" 

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if module_name in self._modules:
            return f"include(\"{module_name}.jl\")"
        elif module_name == ".":
            import_names = []
            for n in names:
                import_names.append(f"include(\"{n}.jl\")")
            return "\n".join(import_names)

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

    def visit_List(self, node:ast.List) -> str:
        elts = self._parse_elts(node)
        if hasattr(node, "is_annotation"):
            return f"{{{elts}}}"
        return (
            f"({elts})"
            if hasattr(node, "lhs") and node.lhs
            else f"[{elts}]"
        )
    
    def visit_Tuple(self, node: ast.Tuple) -> str:
        elts = self._parse_elts(node)
        if hasattr(node, "is_annotation"):
            return elts
        if len(node.elts) == 1:
            return f"({elts},)"
        return f"({elts})"
    
    def _parse_elts(self, node):
        elts = []
        for e in node.elts:
            e_str = self.visit(e)
            if hasattr(node, "is_annotation"):
                elts.append(self._map_type(e_str))
                continue
            elts.append(e_str)
        return ", ".join(elts)

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
            value_type = self._map_type(value)
            index_type = self._map_type(index)
            if value_type == "Tuple":
                return f"({index})"
            return f"{value_type}{{{index_type}}}"

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

        if getattr(node, "step", None):
            step = self.visit(node.step)
            return f"{upper}:{step}:{lower}"

        return f"{lower}:{upper}"


    def visit_Ellipsis(self, node: ast.Ellipsis) -> str:
        return "..."

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
        type_str = self._typename_from_type_node(node.annotation)

        val = None
        if node.value is not None:
            val = self.visit(node.value)

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
                value = self._none_type
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

    def visit_Delete(self, node: ast.Delete) -> str:
        del_targets = []
        for t in node.targets:
            node_name = self.visit(t)
            if isinstance(t, ast.Subscript):
                node_name = self.visit(t.value)

            n_val = node.scopes.find(node_name)
            if type_ann := getattr(n_val, "annotation", None):
                ann_str = self.visit(type_ann)
                if isinstance(t, ast.Subscript) and re.match(r"Dict{\S*}", ann_str):
                    del_targets.append(f"delete!({node_name}, {self.visit(t.slice)})")
                if re.match(r"Vector{\S*}", ann_str) or re.match(r"Dict{\S*}", ann_str):
                    del_targets.append(f"empty!({node_name})")

            del_targets.append(f"#Delete Unsupported\ndel({node_name})")
        
        return "\n".join(del_targets)

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
        args_list = self._get_args(node)
        args = ", ".join(args_list)

        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)

        if hasattr(node, "returns") and node.returns:
            f"@async function {node.name} ({args})::{self.visit(node.returns)}\n{body}end"

        return f"@async function {node.name}({args})\n{body}\nend"

    def visit_Yield(self, node: ast.Yield) -> str:
        func_scope = find_closest_scope(node.scopes)
        if isinstance(func_scope, ast.FunctionDef):
            if RESUMABLE in func_scope.parsed_decorators:
                return f"@yield {self.visit(node.value)}" \
                    if node.value \
                    else "@yield"
            else:
                if node.value:
                    return f"put!(ch_{func_scope.name}, {self.visit(node.value)})"
                else:
                    raise AstUnsupportedOperation(
                            "yield requires a value when using channels", node)

    def visit_YieldFrom(self, node: ast.YieldFrom) -> str:
        # Currently not supported
        return f"# Unsupported\n@yield_from {self.visit(node.value)}"

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

    def visit_Nonlocal(self, node: ast.Nonlocal) -> str:
        names = ", ".join(node.names)
        return f"# Not Supported\n# nonlocal {names}"

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

    def visit_Constructor(self, node: juliaAst.Constructor) -> Any:
        # Get constructor arguments
        args = self._get_args(node, is_constructor=True)
        args_no_defaults = list(map(lambda x: x.split("=")[0], args))
        decls = list(map(lambda x: x.split("::")[0], args_no_defaults))

        args_str = ", ".join(args)
        decls_str = ", ".join(decls)

        # Visit constructor Body
        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)

        struct_name = self.visit(node.struct_name)


        if body:
            return f"""
            {struct_name}({args_str}) = begin
                {body}
                new({decls_str})
            end"""
        return f"{struct_name}({args_str}) = new({decls_str})"

    def visit_LetStmt(self, node: juliaAst.LetStmt) -> Any:
        args = [self.visit(arg) for arg in node.args]
        args_str = ", ".join(args)

        # Visit let body
        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)

        return f"let {args_str}\n{body}\nend"