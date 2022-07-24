from enum import IntFlag
import ast

import re

from py2many.exceptions import AstUnsupportedOperation
from pyjl.global_vars import RESUMABLE
from pyjl.helpers import is_dir, is_file

import pyjl.juliaAst as juliaAst

from .clike import JULIA_INTEGER_TYPES, JULIA_NUM_TYPES, CLikeTranspiler
from .plugins import (
    DECORATOR_DISPATCH_TABLE,
    JULIA_SPECIAL_ASSIGNMENT_DISPATCH_TABLE,
    MODULE_DISPATCH_TABLE,
    DISPATCH_MAP,
)

from py2many.analysis import get_id, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.clike import _AUTO_INVOKED
from py2many.tracer import find_closest_scope, find_in_body, find_node_by_name_and_type, is_class_or_module, is_class_type

from typing import Any, List

SPECIAL_CHARACTER_MAP = {
    "\a": "\\a", 
    "\b": "\\b",
    "\f": "\\f", 
    "\r": "\\r", 
    "\v": "\\v", 
    "\t": "\\t",
    "\xe9":"\\xe9",
    "\000":"\\000",
    "\xff": "\\xff",
    "\x00": "\\x00",
    "\0": "\\0",
    "\ud800": "\\ud800",
    "\udfff": "\\udfff",
    "\udcdc": "\\udcdc",
    "\udad1": "\\udad1",
    "\ud8f0": "\\ud8f0",
    "\x80": "\\x80",
}

# For now just includes SPECIAL_CHARACTER_MAP
DOCSTRING_TRANSLATION_MAP = SPECIAL_CHARACTER_MAP 

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

        # Added
        self._julia_num_types = JULIA_NUM_TYPES
        self._julia_integer_types = JULIA_INTEGER_TYPES
        self._str_special_character_map = STR_SPECIAL_CHARACTER_MAP
        self._bytes_special_character_map = BYTES_SPECIAL_CHARACTER_MAP
        self._docstr_special_character_map = DOCSTRING_TRANSLATION_MAP
        self._special_method_table = self.SPECIAL_METHOD_TABLE

    def comment(self, text: str) -> str:
        return f"#= {text} =#"

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def visit_Constant(self, node: ast.Constant, quotes = True, docstring = False) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return self._none_type
        elif isinstance(node.value, str):
            return self.visit_Str(node, quotes, docstring)
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

    def visit_Str(self, node: ast.Str, quotes = True, docstring = False) -> str:
        # Escape special characters
        trs_map = self._str_special_character_map \
            if not docstring \
            else self._docstr_special_character_map
        node_str = node.value.translate(str.maketrans(trs_map))
        # node_str = node.value.encode("UTF-8").decode("ascii", "backslashreplace") # Avoid special characters
        return f'"{node_str}"' if quotes else node_str

    def visit_Bytes(self, node: ast.Bytes) -> str:
        bytes_str: str = str(node.s)
        content = bytes_str[2:-1]
        bytes_str = content.translate(str.maketrans(self._bytes_special_character_map))
        return f"b\"{bytes_str}\""
        # return 'b"' + node.value.decode("ascii", "backslashreplace") + '"'

    def visit_FunctionDef(self, node: ast.FunctionDef) -> str:
        typedecls = []

        # Parse function args
        args_list = self._get_args(node)
        if hasattr(node, "oop"):
            f_arg = args_list[0].split("::")[0]
            if f_arg == "self":
                # Remove annotation
                args_list[0] = f_arg
        args = ", ".join(args_list)
        node.parsed_args = args

        # Parse return type
        return_type = ""
        if not is_void_function(node):
            if node.returns:
                func_typename = self._typename_from_annotation(node, attr="returns")
                mapped_type = self._map_type(func_typename)
                if mapped_type:
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

    def _get_args(self, node) -> list[str]:
        typenames, args = self.visit(node.args)
        args_list = []

        if len(typenames) > 0 and \
                (typenames[0] == self._default_type or not typenames[0]) \
                and hasattr(node, "self_type"):
            typenames[0] = node.self_type

        defaults = node.args.defaults
        len_defaults = len(defaults)
        len_args = len(args)
        for i in range(len_args):
            arg = args[i]
            arg_typename = typenames[i]

            if arg_typename and arg_typename != "T":
                arg_typename = self._map_type(arg_typename)

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
            if arg_typename and arg_typename != self._default_type:
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

        if dispatch := getattr(node, "dispatch", None):
            fname = self.visit(dispatch.func)
            vargs = self._get_call_args(dispatch)
            ret = self._dispatch(dispatch, fname, vargs)
            if ret is not None:
                return ret

        if not value_id:
            value_id = ""
        
        if getattr(node, "is_annotation", False):
            return self._map_type(f"{value_id}.{attr}")

        return f"{value_id}.{attr}"

    def visit_Call(self, node: ast.Call) -> str:
        if isinstance(node.func, ast.Attribute):
            fname = get_id(node.func)
        else:
            fname = self.visit(node.func)
        class_scope = find_node_by_name_and_type(fname, ast.ClassDef, node.scopes)[0]
        kw_args = not class_scope
        vargs = self._get_call_args(node, kw_args=kw_args)

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret

        # Check if first arg is of class type.
        # If it is, search for the function in the class scope
        fndef = node.scopes.find(fname)
        if vargs and (arg_cls_scope := find_node_by_name_and_type(vargs[0], ast.ClassDef, node.scopes)[0]):
            fndef = arg_cls_scope.scopes.find(fname)

        if fndef and hasattr(fndef, "args") and \
                getattr(fndef.args, "args", None):
            converted = []
            for varg, fnarg, node_arg in zip(vargs, fndef.args.args, node.args):
                actual_type = self._generic_typename_from_annotation(node_arg)
                declared_type = self._generic_typename_from_annotation(fnarg)
                if declared_type and actual_type and declared_type != self._default_type \
                        and actual_type != self._default_type and actual_type != declared_type and \
                        not actual_type.startswith("Optional"): # TODO: Skip conversion of Optional for now
                    converted.append(f"convert({declared_type}, {varg})")
                else:
                    converted.append(varg)
        else:
            converted = vargs

        args = ", ".join(converted)
        return f"{fname}({args})"

    def _get_call_args(self, node: ast.Call, kw_args = True):
        vargs = []
        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            kw_visitor = lambda x: self.visit(x) if kw_args else self.visit(x.value)
            vargs += [kw_visitor(kw) for kw in node.keywords]
        return vargs

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
        left_jl_ann: str = self._typename_from_type_node(
            getattr(node.left, "annotation", self._default_type), 
            default=self._default_type)
        right_jl_ann: str = self._typename_from_type_node(
            getattr(node.right, "annotation", self._default_type), 
            default=self._default_type)

        is_list = lambda x: x.startswith("Array") or x.startswith("Vector")
        is_tuple = lambda x: x.startswith("Tuple")

        # Modulo string formatting
        # TODO: Provide two translation alternatives (sprintf)
        if isinstance(node.left, ast.Constant) and \
                isinstance(node.left.value, str) and \
                isinstance(node.op, ast.Mod):
            left = self.visit_Constant(node.left, quotes=False)
            split_str: list[str] = re.split(r"%\w|%.\d\w|%-\d\d\w", left)
            elts = getattr(node.right, "elts", [node.right])
            for i in range(len(split_str)-1):
                e = elts[i]
                if isinstance(e, ast.Constant):
                    split_str[i] += self.visit_Constant(e,quotes=False)
                else:
                    split_str[i] += f"$({self.visit(e)})"
            return f"\"{''.join(split_str)}\""

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
                return f"[{left}; {right}]"

            # Cover Python String concatenation
            if ((isinstance(node.right, ast.Str) and isinstance(node.left, ast.Str))
                    or (right_jl_ann == "String" and left_jl_ann == "String")):
                return f"{left} * {right}"

        # By default, call super
        return super().visit_BinOp(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        if isinstance(node.operand, (ast.Call, ast.Num, ast.Name, ast.Constant)):
            # Shortcut if parenthesis are not needed
            return f"{self.visit(node.op)}{self.visit(node.operand)}"
        return super().visit_UnaryOp(node)

    def visit_ClassDef(self, node: ast.ClassDef) -> str:
        # Get class declarations and assignments
        self._visit_class_fields(node)

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(self.visit(b))
        body = "\n".join(body)

        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        # Visit decorators
        for ((d_id, _), decorator) in zip(node.parsed_decorators.items(), node.decorator_list):
            if d_id in DECORATOR_DISPATCH_TABLE:
                dec_ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if dec_ret:
                    return dec_ret

        struct_name = get_id(node)
        bases = []
        for base in node.jl_bases:
            bases.append(self.visit(base))

        if bases:
            bases_str = f"{{{', '.join(bases)}}}" if len(bases) > 1 else bases[0]
            struct_def = f"mutable struct {struct_name} <: {bases_str}"
        else:
            struct_def = f"mutable struct {struct_name}"

        docstring = self._get_docstring(node)
        maybe_docstring = f"{docstring}\n" if docstring else ""
        maybe_constructor = f"\n{self.visit(node.constructor)}" if hasattr(node, "constructor") else ""

        if getattr(node, "oop", False):
            self._usings.add("ObjectOriented")
            return f"""@oodef {struct_def}
                            {node.fields_str}
                            {maybe_constructor}
                            {body}
                        end"""

        return f"{struct_def}\n{maybe_docstring}{node.fields_str}{maybe_constructor}\nend\n{body}"

    def _visit_class_fields(self, node):
        declarations: dict[str, (str, Any)] = node.declarations_with_defaults

        dec_items = []
        if not hasattr(node, "constructor_args"):
            has_defaults = any(list(map(lambda x: x[1][1] is not None, declarations.items())))
            # Reorganize fields, so that defaults are last
            dec_items = sorted(declarations.items(), key = lambda x: (x[1][1] != None, x), reverse=False) \
                if has_defaults \
                else declarations.items()
        else:
            init_args = [arg.arg for arg in node.constructor_args.args]
            for arg in init_args:
                if arg in declarations:
                    dec_items.append((arg, declarations[arg]))
            for assign in node.assigns:
                target = assign.targets[0] \
                    if isinstance(assign, ast.Assign) else assign.target
                ann = getattr(target, "annotation", None)
                typename = ast.unparse(ann) if ann else None
                dec_items.append((ast.unparse(target), (typename, ast.unparse(assign.value))))

        decs = []
        fields = []
        fields_str = []
        for declaration, (typename, default) in dec_items:
            dec = declaration.split(".")
            if dec[0] == "self" and len(dec) > 1:
                declaration = dec[1]
            if declaration in self._julia_keywords:
                declaration = f"{declaration}_"

            if is_class_or_module(typename, node.scopes):
                typename = f"Abstract{typename}"

            decs.append(declaration)
            fields_str.append(declaration 
                if (not typename or (typename and typename == self._default_type)) 
                else f"{declaration}::{typename}")
            
            # Default field values
            fields.append((declaration, typename, default))

        node.fields = fields
        node.fields_str = "\n".join(fields_str)

    def visit_StrEnum(self, node) -> str:
        return self._visit_enum(node, "String", str)

    def visit_IntEnum(self, node) -> str:
        return self._visit_enum(node, "Int64", int)

    def visit_IntFlag(self, node: IntFlag) -> str:
        return self._visit_enum(node, "Int64", IntFlag)

    def _visit_enum(self, node, typename: str, caller_type) -> str:
        declarations = node.class_assignments.items()
        sep = "=>" if typename == "String" else "="

        fields = []
        for i, (field, value) in enumerate(declarations):
            val = self.visit(value)
            if val == _AUTO_INVOKED:
                if caller_type == IntFlag:
                    val = 1 << i
                elif caller_type == int:
                    val = i
                elif caller_type == str:
                    val = f'"{value}"'
            fields.append(f"{field} {sep} {val}")
        field_str = "\n".join(fields)

        if("unique" in node.parsed_decorators or typename in self._julia_integer_types):
            return f"@enum {node.name} begin\n{field_str}end"
        else:
            # Cover case where values are not unique and not strings
            self._usings.add("SuperEnum")
            return f"@se {node.name} begin\n{field_str}end"

    def _import(self, name: str, alias: str) -> str:
        '''Formatting Julia Imports'''
        if name in MODULE_DISPATCH_TABLE:
            name = MODULE_DISPATCH_TABLE[name] 
        import_str = self._get_import_str(name)
        if import_str:
            if self._use_modules:
                # Module has the same name as file
                mod_name = name.split(".")[-1]
                if alias:
                    return f"{import_str}\nimport {mod_name} as {alias}"
            return import_str

        import_str = f"import {name}"
        return f"{import_str} as {alias}" if alias else import_str

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if module_name == ".":
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

        import_str = self._get_import_str(module_name)
        if import_str:
            if self._use_modules:
                import_names = f"using {module_name}: {', '.join(names)}"
                return "\n".join([import_str, import_names])
            else:
                # If it imports a file that defines no module, just use "include"
                return import_str

        str_imports = ", ".join(imports)
        return f"using {jl_module_name}: {str_imports}"

    def _get_import_str(self, name: str):
        if (is_mod := is_file(name, self._basedir)) or \
                (is_folder := is_dir(name, self._basedir)):
            # Find path from current file
            extension = ""
            if is_mod:
                extension = ".jl"
            elif is_folder and not is_mod:
                extension = ".__init__.jl"
            sep = "/"
            import_path = name.split(".")
            out_filepath = self._filename.as_posix().split("/")
            if out_filepath[:-1] == import_path[:-1]:
                # Shortcut if paths are the same
                return f'include(\"{import_path[-1]}{extension}\")'
            i, j = len(import_path) - 2, len(out_filepath) - 2
            rev_cnt = 0
            match = False
            while i >= 0 and j >= 0:
                if import_path[i] != out_filepath[j]:
                    rev_cnt += 1
                else:
                    match = True
                i, j = i - 1, j - 1
            if match and rev_cnt > 0 and rev_cnt < len(import_path):
                rev_path = "../" * rev_cnt
                parsed_path = sep.join(import_path[rev_cnt:])
                return f'include(\"{rev_path}{parsed_path}{extension}\")'
            return f'include(\"{sep.join(import_path)}{extension}\")'
        return None

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
            if value == "Optional":
                return f"Union{{{index_type}, Nothing}}"
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
            if isinstance(node.step, ast.UnaryOp) and \
                    isinstance(node.step.op, ast.USub):
                return f"{upper}:{step}:{lower}"
            else:
                return f"{lower}:{step}:{upper}"

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
    
    def visit_Assign(self, node: ast.Assign) -> str:
        value = self.visit(node.value)
        if len(node.targets) == 1:
            if (target := self.visit(node.targets[0])) in JULIA_SPECIAL_ASSIGNMENT_DISPATCH_TABLE:
                return JULIA_SPECIAL_ASSIGNMENT_DISPATCH_TABLE[target](self, node, value)
            
        targets = [self.visit(target) for target in node.targets]
        if value == None:
            value = self._none_type

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

        op = f".=" if getattr(node, "broadcast", False) \
            else "="
        return f"{'='.join(targets)} {op} {value}"

    def visit_Delete(self, node: ast.Delete) -> str:
        del_targets = []
        for t in node.targets:
            # Get node name
            if isinstance(t, ast.Subscript):
                node_name = self.visit(t.value)
            else:
                node_name = self.visit(t)

            type_ann = None
            if t_ann := getattr(t, "annotation", None):
                type_ann = t_ann
            elif n_ann := getattr(node.scopes.find(node_name), "annotation", None):
                type_ann = n_ann
            if isinstance(t, ast.Subscript):
                node_name = self.visit(t.value)

            if type_ann and (ann_str := self.visit(type_ann)):
                if ann_str.startswith("Dict"):
                    if isinstance(t, ast.Subscript):
                        del_targets.append(f"delete!({node_name}, {self.visit(t.slice)})")
                    else:
                        del_targets.append(f"delete!({node_name})")
                elif ann_str.startswith("Vector") or ann_str.startswith("Array"):
                    del_targets.append(f"empty!({node_name})")
            
        if not del_targets:
            del_targets.extend(["#Delete Unsupported", f"del({node_name})"])
        
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

    def visit_JoinedStr(self, node: ast.JoinedStr) -> str:
        str_repr = []
        for value in node.values:
            if isinstance(value, ast.Constant):
                str_repr.append(self.visit_Constant(value, quotes=False))
            elif isinstance(value, ast.FormattedValue):
                str_repr.append(f"$({self.visit(value)})")
            else:
                str_repr.append(self.visit(value))
        return f"\"{''.join(str_repr)}\""

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
                f_spec_split = f_spec_val.split(".")
                if len(f_spec_split) > 1:
                    f_spec_parsed = f_spec_split[1].replace("\"", "")
                else:
                    f_spec_parsed = f_spec_val
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

    def visit_LetStmt(self, node: juliaAst.LetStmt) -> Any:
        args = [self.visit(arg) for arg in node.args]
        args_str = ", ".join(args)

        # Visit let body
        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)

        return f"let {args_str}\n{body}\nend"

    def visit_JuliaModule(self, node: juliaAst.JuliaModule) -> Any:
        body = self.visit_Module(node)
        mod_name = self.visit(node.name)
        return f"module {mod_name}\n{body}\nend"

    def visit_OrderedDict(self, node: juliaAst.OrderedDict):
        self._usings.add("OrderedCollections")
        kv_pairs = []
        for key, value in zip (node.keys, node.values):
            if key:
                kv_pairs.append(f"{self.visit(key)} => {self.visit(value)}")
            else:
                if isinstance(value, ast.Dict):
                    kv_pairs.append(f"{self.visit(value)}...")
        
        kv_pairs = ", ".join(kv_pairs)
        return f"OrderedDict({kv_pairs})"

    def visit_OrderedDictComp(self, node: juliaAst.OrderedDictComp):
        self._usings.add("OrderedCollections")
        key = self.visit(node.key)
        value = self.visit(node.value)
        generators = node.generators
        dict_comp = (f"{key} => {value} " +
                     self._visit_generators(generators))

        return f"OrderedDict({dict_comp})"

    def visit_OrderedSet(self, node: juliaAst.OrderedDict):
        self._usings.add("OrderedCollections")
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"OrderedSet([{elements_str}])"

    def visit_Constructor(self, node: juliaAst.Constructor):
        args = self._get_args(node)
        if args and args[0].split("::")[0] == "self":
            # Remove self
            args = args[1:]
        args_str = ", ".join(args)

        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        body = "\n".join(body)

        if len(node.body) == 1 and isinstance(node.body[0], ast.Call) \
                and get_id(node.body[0].func) == "new":
            return f"{node.name}({args_str}) = {body}"
        else:
            return f"""{node.name}({args_str}) = begin
                            {body}
                        end"""

    def visit_Block(self, node: juliaAst.Block) -> Any:
        body = []
        for n in node.body:
            body.append(self.visit(n))
        body = "\n".join(body)
        if getattr(node, "decorator_list", None):
            decorators = " ".join(list(map(lambda x: f"@{self.visit(x)}", node.decorator_list)))
            return f"{decorators} {node.name} begin\n{body}\nend"
        return f"{node.name} begin\n{body}\nend"

    def visit_Symbol(self, node: juliaAst.Symbol) -> Any:
        return f":{node.id}"