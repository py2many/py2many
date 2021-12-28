import ast
from build.lib.py2many.exceptions import AstTypeNotSupported
from py2many.input_configuration import ParseFileStructure
from pathlib import Path

import textwrap
import re

from pyjl.helpers import get_range_from_for_loop

from .clike import CLikeTranspiler
from .plugins import (
    ATTR_DISPATCH_TABLE,
    DECORATOR_DISPATCH_TABLE,
    CONTAINER_TYPE_MAP,
    FUNC_DISPATCH_TABLE,
    DECORATOR_MAP,
    INTEGER_TYPES,
    MODULE_DISPATCH_TABLE,
    DISPATCH_MAP,
    NUM_TYPES,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.clike import _AUTO_INVOKED
from py2many.tracer import find_in_body, find_node_matching_type, find_node_matching_name_and_type, get_class_scope, is_class_type, is_list, is_enum

from typing import Any, Dict, List, OrderedDict, Tuple, Union

_DEFAULT = "Any"

def julia_decorator_rewriter(tree, input_config):
    JuliaDecoratorRewriter(input_config).visit(tree)

def get_decorator_id(decorator):
    id = get_id(decorator.func) if isinstance(decorator, ast.Call) else get_id(decorator)
    # TODO: Check if this is the correct implementation
    if isinstance(id, list): 
        id = id[0]
    return id

class JuliaMethodCallRewriter(ast.NodeTransformer):
    def visit_Call(self, node):
        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]

        fname = node.func
        if isinstance(fname, ast.Attribute):
            if is_list(node.func.value) and fname.attr == "append":
                new_func_name = "push!"
            else:
                new_func_name = fname.attr

            if get_id(fname.value):
                node0 = ast.Name(id=get_id(fname.value), lineno=node.lineno)
            else:
                node0 = fname.value

            if new_func_name == "join":
                # Join with empty string if no content is present
                if not node0:
                    node0 = f"\"\""
                args = node.args + [node0]
            else:
                args = [node0] + node.args
            
            node.func = ast.Name(id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        if isinstance(fname, ast.Name):
            if get_id(node.func) == "join" and node.args:
                args.reverse()

        node.args = args
        return node


class JuliaDecoratorRewriter(ast.NodeTransformer):
    def __init__(self, input_config: Dict) -> None:
        super().__init__()
        self._input_config_map = input_config

    def visit_FunctionDef(self, node):
        node_name = get_id(node)
        node_scope_name = None
        if len(node.scopes) > 2:
            node_class = find_node_matching_type(ast.ClassDef, node.scopes)
            node_scope_name = get_id(node_class) if node_class else None
        
        node_field_map = ParseFileStructure.get_function_attributes(node_name, 
            node_scope_name, self._input_config_map)
        
        if "decorators" in node_field_map:
            node.decorator_list += node_field_map["decorators"]
            # Remove duplicates
            node.decorator_list = list(set(node.decorator_list))
            # Transform in Name nodes
            node.decorator_list = list(map(lambda dec: ast.Name(id=dec), node.decorator_list))

        self._populate_decorator_map(node, node_scope_name)
        return node

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        class_name = get_id(node)
        if self._input_config_map:
            node_field_map = ParseFileStructure.get_class_attributes(class_name, self._input_config_map)
            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(map(lambda dec: ast.Name(id=dec), node.decorator_list))

        self._populate_decorator_map(node, None)
        return node

    # Decorator map is required by some functions to know which annotations are in use
    def _populate_decorator_map(self, node, node_scope_name) -> None:
        DECORATOR_MAP[node.name] = []
        node_dict = {"type": type(node), "decorators": []}
        for decorator in node.decorator_list:
            node_dict["decorators"].append(get_decorator_id(decorator))
        DECORATOR_MAP[(node.name, node_scope_name)] = node_dict



class JuliaYieldRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()
        # loop -> contains loop variables
        # func -> contains function specific fields: (func_name, yield_cnt, decorator_list)
        self._scope_stack: Dict[str, list] = {"loop": [], "func": []}
        self._func_map: Dict[str, Dict] = {}
    
    def visit_Module(self, node) -> str:
        for b in node.body:
            if not isinstance(b, ast.FunctionDef):
                self.visit(b)

        # Second pass to handle functiondefs whose body
        # may refer to other members of node.body
        visit_after = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                # Some funtions might have precedence over others
                v_node = find_in_body(b.body, (lambda x: isinstance(x, ast.YieldFrom)))
                if v_node:
                    visit_after.append(b)
                else:
                    self.visit(b)

        for b in visit_after:
            self.visit(b)
        return node
    
    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        decorator_list_str = list(map(get_decorator_id, node.decorator_list))

        # Fill scope variables
        self._scope_stack["func"].append({"func_name": get_id(node), 
            "yield_cnt": 0, "decorator_list": decorator_list_str, 
            "for_loop_range": 0})

        # visit nodes in body
        for n in node.body:
            self.visit(n)

        # Add to func_map
        self._func_map[get_id(node)] = {"yield_cnt": self._scope_stack["func"][-1]["yield_cnt"], 
            "decorator_list": decorator_list_str}

        if "use_continuables" not in decorator_list_str:
            # Build a channel with the necessary size (number of yields in a function)
            func_data = self._scope_stack["func"][-1]
            if func_data["yield_cnt"] > 0:
                func_name, size = get_id(node), func_data["yield_cnt"]
                channel = ast.Assign(targets = [ast.Name(id = f"channel_{func_name}")], 
                    value = ast.Name(id = f"Channel({size})"))
                channel_close = ast.Call(func = ast.Name(id = f"close", lineno=node.lineno), args = [ast.Name(id = f"(channel_{func_name})")],
                    keywords = [], lineno=node.lineno, col_offset = node.col_offset)
                return_val = ast.Return(value = ast.Name(f"channel_{func_name}"), lineno=node.lineno, col_offset = node.col_offset)

                # Append to the function body
                node.body = [channel] + node.body
                node.body.extend([channel_close, return_val])
        
        self._scope_stack["func"].pop()
        return node

    def visit_Yield(self, node: ast.Yield) -> Any:
        func_node = self._scope_stack["func"][-1]
        decorators = []
        if func_node:
            if func_node["for_loop_range"] != 0:
                func_node["yield_cnt"] = func_node["for_loop_range"]
            else:
                func_node["yield_cnt"] += 1
            decorators = func_node["decorator_list"]

        if "use_continuables" in decorators:
            node = ast.Call(func = ast.Name(id = "cont"), args = [ast.Name(id = f"{self.visit(node.value)}")], 
                keywords = [], lineno=node.lineno, col_offset = node.col_offset)
        else:
            if node.value:
                func_name = func_node["func_name"]
                node = ast.Yield(value = ast.Call (func = ast.Name(id = "put!"), args = [
                    ast.Name(id = f"channel_{func_name}" if func_node else "channel_module"),
                    node.value], keywords = [], lineno = node.lineno,
                    col_offset = node.col_offset))
            else:
                node = ast.Yield(value = ast.Name(id = ""))

        return node

    def visit_YieldFrom(self, node: ast.YieldFrom) -> Any:
        # get current function
        func_node = self._scope_stack["func"][-1]
        func_name = func_node["func_name"]
        decorators = func_node["decorator_list"] if func_node else []

        range = 0
        if isinstance(node.value, ast.Call) and hasattr(node.value, "func"):
            # get function being called
            yield_func_call = get_id(node.value.func)
            if yield_func_call in self._func_map:
                # Add yield_cnt to current function
                range = self._func_map[yield_func_call]["yield_cnt"]
                func_node["yield_cnt"] += range

        if "use_continuables" in decorators:
            node = ast.YieldFrom(value = ast.For(
                        target = ast.Name(id=f"value_{func_name}"),
                        iter = node.value,
                        body = [ast.Call(func = ast.Name(id = "cont"), args = [
                                    ast.Name(id =f"value_{func_name}")],
                                keywords = [], lineno = node.lineno)]))
        else:
            node = ast.YieldFrom(value = ast.For(
                    target = ast.Name(id = f"value_{func_name}"),
                    iter = node.value,
                    body = [ast.Call(func = ast.Name(id = "put!"), 
                            args = [ast.Name(id = f"channel_{func_name}"), 
                                ast.Name(id = f"value_{func_name}")],
                            keywords = [], lineno = node.lineno)]))
        return node

    def visit_For(self, node: ast.For) -> Any:
        # Get current function
        curr_func = self._scope_stack["func"][-1]

        # Get for loop range (if possible)
        iter = get_range_from_for_loop(node)
        curr_func["for_loop_range"] += iter

        # visit nodes in body
        for n in node.body:
            self.visit(n)

        # Set count to 0 as scope changes
        curr_func["for_loop_range"] = 0
        
        return node


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

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses

    def comment(self, text):
        return f"#= {text} \n=#"

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def visit_Constant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "nothing"
        elif isinstance(node.value, complex):
            str_value = str(node.value)
            return (
                str_value.replace("j", "im") if str_value.endswith("j") else str_value
            )
        else:
            return super().visit_Constant(node)

    def visit_FunctionDef(self, node) -> str:
        # visit function body
        body = ""
        node_body = "\n".join([self.visit(n) for n in node.body])

        # Check for function annotations
        annotation = ""
        annotation_body = ""
        for decorator in node.decorator_list:
            d_id = get_decorator_id(decorator)
            if d_id in DECORATOR_DISPATCH_TABLE:
                ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if ret is not None:
                    [annotation, annotation_body] = ret[0], ret[1]       

        # Adding the body of the node
        body += node_body + annotation_body

        typenames, args = self.visit(node.args)

        args_list = []
        typedecls = []

        is_python_main = getattr(node, "python_main", False)

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
            
            # TODO: Check if this is necessary
            # elif arg_typename == "T":
            #     # Allow the user to know that type is generic
            #     arg_typename = "T{0}".format(index)
            #     typedecls.append(arg_typename)
            #     index += 1

            # Get default parameter values
            default = None
            if defaults:
                if len_defaults != len_args:
                    diff_len = len_args - len_defaults
                    default = defaults[i - diff_len] if i >= diff_len else None
                else:
                    default = defaults[i]

            if get_id(default):
                default = get_id(default)
            elif isinstance(default, ast.Constant):
                default = default.value
                if isinstance(default, str):
                    default = f"\"{default}\""

            arg_signature = ""
            if arg_typename:
                arg_signature = f"{arg}::{arg_typename}" if default is None else f"{arg}::{arg_typename} = {default}"
            else:
                arg_signature = f"{arg}" if default is None else f"{arg} = {default}"
            args_list.append(arg_signature)

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                func_typename = (node.julia_annotation if hasattr(node, "julia_annotation")
                    else super()._map_type(self._typename_from_annotation(node, attr="returns")))
                return_type = f"::{func_typename}"

        template = ""
        if len(typedecls) > 0:
            template = "{{{0}}}".format(", ".join(typedecls))

        args = ", ".join(args_list)
        funcdef = f"{annotation}function {node.name}{template}({args}){return_type}"
        maybe_main = ""
        if is_python_main:
            maybe_main = "\nmain()"
        return f"{funcdef}\n{body}\nend\n{maybe_main}"

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

    def visit_Call(self, node) -> str:
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
                declared_type = self._typename_from_annotation(fnarg) # if fnarg.arg != "self" else None
                if declared_type != None and declared_type != "" and actual_type != declared_type and actual_type != self._default_type:
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

        # Separate name and args
        split_func = re.split(r"[\W']+", it)
        func_name = split_func[0]
        if func_name:
            class_scope = None
            if len(split_func) > 1:
                class_scope = get_class_scope(split_func[1], node.scopes)
            key = (func_name, get_id(class_scope))
            if (key in DECORATOR_MAP
                    and DECORATOR_MAP[key]["type"] == ast.FunctionDef
                    and "use_continuables" in DECORATOR_MAP[key]["decorators"]):
                it = f"collect({it})"

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

    def visit_Str(self, node) -> str:
        # Allow line break translation
        node.value = node.value.replace("\n", "\\n")
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node) -> str:
        bytes_str = node.s
        bytes_str = bytes_str.replace(b'"', b'\\"')
        return 'b"' + bytes_str.decode("ascii", "backslashreplace") + '"'

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

            if hasattr(comparator, "annotation"):
                self._generic_typename_from_annotation(node.comparators[0])
                value_type = getattr(
                    comparator.annotation, "generic_container_type", None
                )
                if value_type and value_type[0] == "Dict":
                    comp_str = f"keys({comp_str})"

            if isinstance(op, ast.In):
                op_str = "in"
            elif isinstance(op, ast.NotIn):
                op_str = "not in"
            elif (isinstance(op, ast.Eq) 
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
            return "Nothing"
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "Nothing"
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
        buf.append("while {0}".format(self.visit(node.test)))
        buf.extend([self.visit(n) for n in node.body])
        buf.append("end")
        return "\n".join(buf)

    def visit_UnaryOp(self, node) -> str:
        if hasattr(node, "op"):
            if isinstance(node.op, ast.USub):
                if isinstance(node.operand, (ast.Call, ast.Num)):
                    # Shortcut if parenthesis are not needed
                    return "-{0}".format(self.visit(node.operand))
                else:
                    return "-({0})".format(self.visit(node.operand))
            elif isinstance(node.op, ast.Invert):
                return f"~{self.visit(node.operand)}"
            else:
                return super().visit_UnaryOp(node)
        return super().visit_UnaryOp(node)

    def visit_BinOp(self, node) -> str:
        left_jl_ann = node.left.julia_annotation
        right_jl_ann = node.right.julia_annotation

        # Visit left and right
        left = self.visit_List(node.left) if isinstance(node.left, ast.List) else self.visit(node.left)
        right = self.visit_List(node.right) if isinstance(node.right, ast.List) else self.visit(node.right)

        if isinstance(node.op, ast.Mult):
            # Cover multiplication between List and Number 
            if((isinstance(node.right, ast.Num) or (right_jl_ann in NUM_TYPES)) and 
                    ((isinstance(node.left, ast.List) or left_jl_ann == "Array" or left_jl_ann == "Vector") or 
                    (isinstance(node.left, ast.Str) or left_jl_ann == "String"))):
                return f"repeat({left},{right})"

            if((isinstance(node.left, ast.Num) or (left_jl_ann in NUM_TYPES)) and 
                    ((isinstance(node.right, ast.List) or right_jl_ann == "Array" or left_jl_ann == "Vector") or
                    (isinstance(node.right, ast.Str) or right_jl_ann == "String"))):
                return f"repeat({right},{left})"

            # Cover Python Int and Boolean multiplication (also supported in Julia)
            if (((isinstance(node.right, ast.Num) or right_jl_ann in NUM_TYPES )
                    and (isinstance(node.left, ast.BoolOp) or left_jl_ann == "Bool")) or
                    ((isinstance(node.left, ast.Num) or left_jl_ann in NUM_TYPES)
                    and (isinstance(node.right, ast.BoolOp) or right_jl_ann == "Bool"))):
                return f"{left}*{right}"

        if isinstance(node.op, ast.Add) :
            # Cover Python list addition
            if ((isinstance(node.right, ast.List) and isinstance(node.left, ast.List)) 
                    or ((right_jl_ann == "Array" or right_jl_ann == "Vector") 
                        and (left_jl_ann == "Array" or left_jl_ann == "Vector"))):
                return f"[{left};{right}]"
            
            # Cover Python String concatenation
            if ((isinstance(node.right, ast.Str) and isinstance(node.left, ast.Str)) 
                    or (right_jl_ann == "String" and left_jl_ann == "String")):
                return f"{left} * {right}"

        if isinstance(node.op, ast.MatMult):
            if(isinstance(node.right, ast.Num) and isinstance(node.left, ast.Num)):
                return "({0}*{1})".format(left, right)

        # By default, call super
        return super().visit_BinOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(JuliaTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        # Allow support for decorator chaining
        annotation, annotation_field, annotation_body, annotation_modifiers = "", "", "", ""
        for decorator in node.decorator_list:
            d_id = get_decorator_id(decorator)
            if (d_id in DECORATOR_DISPATCH_TABLE 
                    and (dec_ret := DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)) 
                        is not None):
                annotation, annotation_field, annotation_modifiers, annotation_body = dec_ret

        fields = []
        for declaration, typename in declarations.items():
            fields.append(declaration if typename == "" else f"{declaration}::{typename}")

        fields = "" if fields == [] else "\n".join(fields) + "\n" + annotation_field
        struct_def = (f"{annotation_modifiers} struct {node.name}\n{fields}end\n" if annotation_modifiers != "" 
            else f"struct {node.name}\n{fields}end\n")
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name
                body.append(b)
        body = "\n".join([self.visit(b) for b in body])
        annotation_body
        return f"{annotation}{struct_def}{body}"
 
    def _visit_enum(self, node, typename: str, fields: List[Tuple]) -> str:
        decorators = [get_decorator_id(d) for d in node.decorator_list]
        field_str = ""
        for field, value in fields:
                field_str += f"\t{field}\n"
        if("unique" in decorators and typename not in INTEGER_TYPES):
            # self._usings.add("Enum")
            return textwrap.dedent(
                f"@enum {node.name}::{typename} begin\n{field_str}end"
            )
        else :
            # Cover case in pyenum where values are unique and strings
            self._usings.add("PyEnum")
            return textwrap.dedent(
                f"@pyenum {node.name}::{typename} begin\n{field_str}end"
            )

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

    def visit_IntFlag(self, node) -> str:
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == _AUTO_INVOKED:
                var = 1 << i
            fields.append((member, var))
        return self._visit_enum(node, "Int64", fields)

    def _import(self, name: str) -> str:
        return f"import {name}" # import or using?

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
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
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{k} => {v}" for k, v in zip(keys, values)])
        return f"Dict({kv_pairs})"

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if index == None:
            return "{0}[(Something, Strange)]".format(value)
        if hasattr(node, "is_annotation"):
            if value in CONTAINER_TYPE_MAP:
                value = CONTAINER_TYPE_MAP[value]
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
            value_type = getattr(node.value.annotation, "generic_container_type", None)
            if (value_type is not None and value_type[0] == "List" 
                    and not isinstance(node.slice, ast.Slice)):
                # Julia array indices start at 1
                return f"{value}[{index} + 1]"

        # Increment index's that use for loop variables  
        split_index = set(filter(None, re.split(r"\(|\)|\[|\]|-|\s|\:", index)))
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

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        # If there is a Julia annotation, get that instead of the 
        # default Python annotation
        type_str = (
            node.julia_annotation 
            if (node.julia_annotation and node.julia_annotation != "None") 
            else type_str
        )
        if not type_str or type_str == self._default_type:
            return f"{target} = {val}"
        return f"{target}::{type_str} = {val}"

    def visit_AugAssign(self, node) -> str:
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2}".format(target, op, val)

    def _visit_AssignOne(self, node, target) -> str:
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
                value = "Nothing"
            return "{0} = {1}".format(target, value)

        definition = node.scopes.parent_scopes.find(get_id(target))
        if definition is None:
            definition = node.scopes.find(get_id(target))

        target_str = self.visit(target)
        value = self.visit(node.value)
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
            type_ann = super()._map_type(self._typename_from_annotation(node_assign))
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

    def visit_AsyncFunctionDef(self, node) -> str:
        return "#[async]\n{0}".format(self.visit_FunctionDef(node))

    def visit_Yield(self, node: ast.Yield) -> str:
        return f"{self.visit(node.value)}"

    def visit_YieldFrom(self, node: ast.YieldFrom) -> str:
        return f"{self.visit(node.value)}"

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

    def visit_DictComp(self, node) -> str:
        key = self.visit(node.key)
        value = self.visit(node.value)
        generators = node.generators
        dict_comp = (f"{key} => {value} " + 
            self._visit_generators(generators))

        return f"Dict({dict_comp})"
    
    def visit_Global(self, node) -> str:
        return "global {0}".format(", ".join(node.names))

    def visit_Starred(self, node) -> str:
        return f"{self.visit(node.value)}..."

    def visit_IfExp(self, node) -> str:
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"{test} ? ({body}) : ({orelse})"

    def _visit_generators(self, generators):
        gen_exp = ""
        for i in range(len(generators)):
            generator = generators[i]
            target = self.visit(generator.target)
            iter = self.visit(generator.iter)
            gen_exp += f"for {target} in {iter}"
            filter_str = ""
            if(len(generator.ifs) == 1):
                filter_str += f" if {self.visit(generator.ifs[0])} "
            else:
                for i in range(0, len(generator.ifs)):
                    gen_if = generator.ifs[i]
                    filter_str += f" if {self.visit(gen_if)}" if i==0 else f" && {self.visit(gen_if)} "
            gen_exp += filter_str 

        return gen_exp
