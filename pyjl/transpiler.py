import ast
import textwrap
from pyjl.helpers import verify_types

from pyjl.plugins import (
    DECORATOR_DISPATCH_TABLE,
    JULIA_SPECIAL_FUNCTIONS,
    MODULE_DISPATCH_TABLE,
)

from .clike import CLikeTranspiler

from py2many.analysis import get_id, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.clike import _AUTO_INVOKED, class_for_typename
from py2many.tracer import (
    find_node_by_name_and_type,
    is_list,
    defined_before,
    is_class_or_module,
    is_enum,
)

from typing import List, Tuple


class JuliaMethodCallRewriter(ast.NodeTransformer):
    def visit_Call(self, node):
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
            node.args = [node0] + node.args
            node.func = ast.Name(id=new_func_name, lineno=node.lineno, ctx=fname.ctx)
        return node


class JuliaTranspiler(CLikeTranspiler):
    NAME = "julia"

    def __init__(self):
        super().__init__()
        self._headers = set([])
        self._default_type = ""

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses

    def comment(self, text):
        return f"# {text}"

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

    def visit_FunctionDef(self, node: ast.FunctionDef) -> str:
        typedecls = []

        # Parse function args
        args_list = self._get_args(node)
        args = ", ".join(args_list)
        node.args_list = args_list
        node.parsed_args = args

        func_generics = set()
        for arg in node.args.args:
            ann = getattr(arg, "annotation", None)
            for g in self._generics:
                if verify_types(ann, g):
                    func_generics.add(g)
        node.maybe_generics = (
            f"where {', '.join(func_generics)}" if func_generics else ""
        )

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

        # Change functions that have the same name as modules
        if self._use_modules and node.name == self._module:
            node.name = f"{node.name}_"

        # Visit special functions:
        if node.name in JULIA_SPECIAL_FUNCTIONS:
            return JULIA_SPECIAL_FUNCTIONS[node.name](self, node)

        # Visit decorators
        for ((d_id, _), decorator) in zip(
            node.parsed_decorators.items(), node.decorator_list
        ):
            if d_id in DECORATOR_DISPATCH_TABLE:
                ret = DECORATOR_DISPATCH_TABLE[d_id](self, node, decorator)
                if ret is not None:
                    return ret

        # Visit function body
        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        body = "\n".join(body)
        if body == "...":
            body = ""

        funcdef = (
            f"function {node.name}{template}({args}){return_type}{node.maybe_generics}"
        )
        return f"{funcdef}\n{body}\nend\n"

    def _get_args(self, node) -> list[str]:
        typenames, args = self.visit(node.args)
        args_list = []

        # Get self type. Only avoid if:
        #  - _oop_nested_funcs is being used, as the @oodef macro will do it automatically.
        #  - the "classmethod" decorator is used
        if (
            len(typenames) > 0
            and (not typenames[0] or typenames[0] == self._default_type)
            and hasattr(node, "self_type")
            and not getattr(node, "_oop_nested_funcs", False)
            and "classmethod" not in node.parsed_decorators
            and "staticmethod" not in node.parsed_decorators
        ):
            if getattr(node, "oop", False):
                typenames[0] = f"@like({node.self_type})"
            else:
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
                arg_signature = (
                    f"{arg}::{arg_typename}"
                    if default is None
                    else f"{arg}::{arg_typename} = {default}"
                )
            else:
                arg_signature = f"{arg}" if default is None else f"{arg} = {default}"
            args_list.append(arg_signature)

        if node.args.vararg:
            _, arg = self.visit(node.args.vararg)
            args_list.append(f"{arg}...")

        return args_list

    def visit_Return(self, node) -> str:
        if node.value:
            return "return {0}".format(self.visit(node.value))
        return "return"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
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

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}::{attr}"

        return f"{value_id}.{attr}"

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(0:{vargs[0]} - 1)"
        elif len(node.args) == 2:
            return f"({vargs[0]}:{vargs[1]} - 1)"
        elif len(node.args) == 3:
            return f"({vargs[0]}:{vargs[2]}:{vargs[1]}-1)"

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def _visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        return f'println(join([{args}], " "))'

    def visit_Call(self, node: ast.Call) -> str:
        node.func.in_call = True
        # Change functions that have the same name as modules
        fname = self.visit(node.func)
        if self._use_modules and fname == self._module:
            fname = f"{fname}_"
        vargs, kwargs = self._get_call_args(node)

        ret = self._dispatch(node, fname, vargs, kwargs)
        if ret is not None:
            if isinstance(node.scopes[-1], ast.Try):
                call_func = ret.split("(")[0].split(".")
                c_list = []
                for c in call_func:
                    c_list.append(c)
                    if ".".join(c_list) in self._pycall_imports:
                        self._is_pycall_exception = True
            return ret

        # Check if first arg is of class type.
        # If it is, search for the function in the class scope
        fndef = node.scopes.find(fname)
        if vargs and (
            arg_cls_scope := find_node_by_name_and_type(
                vargs[0], ast.ClassDef, node.scopes
            )[0]
        ):
            fndef = arg_cls_scope.scopes.find(fname)

        if fndef and hasattr(fndef, "args") and getattr(fndef.args, "args", None):
            fndef_args = fndef.args.args
            if "staticmethod" in getattr(fndef, "parsed_decorators", {}) and len(
                vargs
            ) > len(fndef_args):
                # Compensate for self argument
                fndef_args = [ast.arg(arg="self")] + fndef_args
            converted = []
            for varg, fnarg, node_arg in zip(vargs, fndef_args, node.args):
                actual_type = self._typename_from_annotation(node_arg)
                declared_type = self._typename_from_annotation(fnarg)
                if (
                    declared_type
                    and actual_type
                    and declared_type != self._default_type
                    and actual_type != self._default_type
                    and actual_type != declared_type
                    and not actual_type.startswith("Optional")
                ):  # TODO: Skip conversion of Optional for now
                    converted.append(f"convert({declared_type}, {varg})")
                else:
                    converted.append(varg)
        else:
            converted = vargs

        # Join kwargs to converted vargs
        converted.extend([f"{k[0]} = {k[1]}" for k in kwargs])

        args = ", ".join(converted)
        return f"{fname}({args})"

    def _get_call_args(self, node: ast.Call):
        vargs = []
        kwargs = []
        if node.args:
            for a in node.args:
                vargs.append(self.visit(a))
        if node.keywords:
            for n in node.keywords:
                arg_str = n.arg if n.arg not in self._julia_keywords else f"{n.arg}_"
                kwargs.append((arg_str, self.visit(n.value)))
        return vargs, kwargs

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for {0} in {1}".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("end")
        return "\n".join(buf)

    def visit_Str(self, node) -> str:
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node) -> str:
        bytes_str = node.s
        bytes_str = bytes_str.replace(b'"', b'\\"')
        return 'b"' + bytes_str.decode("ascii", "backslashreplace") + '"'

    def visit_Compare(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])

        if hasattr(node.comparators[0], "annotation"):
            self._generic_typename_from_annotation(node.comparators[0])
            value_type = getattr(
                node.comparators[0].annotation, "generic_container_type", None
            )
            if value_type and value_type[0] == "Dict":
                right = f"keys({right})"

        if isinstance(node.ops[0], ast.In):
            return "{0} in {1}".format(left, right)
        elif isinstance(node.ops[0], ast.NotIn):
            return "{0} not in {1}".format(left, right)

        return super().visit_Compare(node)

    def visit_Name(self, node) -> str:
        if node.id == "None":
            return "None"
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node) -> str:
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "None"
        else:
            return super().visit_NameConstant(node)

    def visit_If(self, node) -> str:
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        buf = []
        cond = self.visit(node.test)
        buf.append(f"if {cond}")
        buf.extend([self.visit(child) for child in node.body])

        orelse = [self.visit(child) for child in node.orelse]
        if orelse:
            buf.append("else\n")
            buf.extend(orelse)
            buf.append("end")
        else:
            buf.append("end")

        return "\n".join(buf)

    def visit_While(self, node) -> str:
        buf = []
        buf.append("while {0}".format(self.visit(node.test)))
        buf.extend([self.visit(n) for n in node.body])
        buf.append("end")
        return "\n".join(buf)

    def visit_UnaryOp(self, node) -> str:
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super().visit_UnaryOp(node)

    def visit_BinOp(self, node) -> str:
        if (
            isinstance(node.left, ast.List)
            and isinstance(node.op, ast.Mult)
            and isinstance(node.right, ast.Num)
        ):
            return "std::vector ({0},{1})".format(
                self.visit(node.right), self.visit(node.left.elts[0])
            )
        elif isinstance(node.op, ast.MatMult):
            return "({0}*{1})".format(self.visit(node.left), self.visit(node.right))
        else:
            return super().visit_BinOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(JuliaTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        decorators = [get_id(d) for d in node.decorator_list]
        decorators = [
            class_for_typename(t, None, self._imported_names) for t in decorators
        ]
        for d in decorators:
            if d in DECORATOR_DISPATCH_TABLE:
                ret = DECORATOR_DISPATCH_TABLE[d](self, node)
                if ret is not None:
                    return ret

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append(f"{declaration}::{typename}")

        fields = "\n".join(fields)
        struct_def = f"struct {node.name}\n{fields}\nend\n"
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name
        body = "\n".join([self.visit(b) for b in node.body])
        return f"{struct_def}\n{body}"

    def _visit_enum(self, node, typename: str, fields: List[Tuple]) -> str:
        self._usings.add("SuperEnum")
        fields_list = []

        sep = "=>" if typename == "String" else "="
        for field, value in fields:
            fields_list += [
                f"""\
                {field} {sep} {value}
            """
            ]
        fields_str = "".join(fields_list)
        return textwrap.dedent(
            f"""\
            @se {node.name} begin\n{fields_str}
            end
            """
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
        return f"import {name}"

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if len(names) == 1:
            # TODO: make this more generic so it works for len(names) > 1
            name = names[0]
            lookup = f"{module_name}.{name}"
            if lookup in MODULE_DISPATCH_TABLE:
                jl_module_name, jl_name = MODULE_DISPATCH_TABLE[lookup]
                jl_module_name = jl_module_name.replace(".", "::")
                return f"using {jl_module_name}: {jl_name}"
        module_name = module_name.replace(".", "::")
        names = ", ".join(names)
        return f"using {module_name}: {names}"

    def visit_List(self, node) -> str:
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"[{elements_str}]"

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
        if hasattr(node, "is_annotation"):
            if value in self.CONTAINER_TYPE_MAP:
                value = self.CONTAINER_TYPE_MAP[value]
            if value == "Tuple":
                return "({0})".format(index)
            return "{0}{{{1}}}".format(value, index)
        # TODO: optimize this. We need to compute value_type once per definition
        self._generic_typename_from_annotation(node.value)
        if hasattr(node.value, "annotation"):
            value_type = getattr(node.value.annotation, "generic_container_type", None)
            if value_type is not None and value_type[0] == "List":
                # Julia array indices start at 1
                return "{0}[{1} + 1]".format(value, index)

        return "{0}[{1}]".format(value, index)

    def visit_Index(self, node) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node) -> str:
        lower = ""
        if node.lower:
            lower = self.visit(node.lower)
        upper = ""
        if node.upper:
            upper = self.visit(node.upper)

        return "{0}..{1}".format(lower, upper)

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
        if type_str == self._default_type:
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
                value = "None"
            return "{0} = {1}".format(target, value)

        definition = node.scopes.parent_scopes.find(get_id(target))
        if definition is None:
            definition = node.scopes.find(get_id(target))
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target_str = self.visit(target)
            value = self.visit(node.value)
            return f"{target_str} = {value};"
        else:
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value}"

    def visit_Delete(self, node) -> str:
        target = node.targets[0]
        return "{0}.drop()".format(self.visit(target))

    def visit_Raise(self, node) -> str:
        if node.exc is not None:
            return "throw({0})".format(self.visit(node.exc))
        # This handles the case where `raise` is used without
        # specifying the exception.
        return "error()"

    def visit_Await(self, node) -> str:
        return "await!({0})".format(self.visit(node.value))

    def visit_AsyncFunctionDef(self, node) -> str:
        return "#[async]\n{0}".format(self.visit_FunctionDef(node))

    def visit_Yield(self, node) -> str:
        return "//yield is unimplemented"

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
        dict_comp = f"{key} => {value} " + self._visit_generators(generators)

        return f"Dict({dict_comp})"

    def _visit_generators(self, generators):
        gen_exp = []
        for i in range(len(generators)):
            generator = generators[i]
            target = self.visit(generator.target)
            iter = self.visit(generator.iter)
            exp = f"for {target} in {iter}"
            gen_exp.append(exp) if i == 0 else gen_exp.append(f" {exp}")
            filter_str = ""
            if len(generator.ifs) == 1:
                filter_str += f" if {self.visit(generator.ifs[0])} "
            else:
                for i in range(0, len(generator.ifs)):
                    gen_if = generator.ifs[i]
                    filter_str += (
                        f" if {self.visit(gen_if)}"
                        if i == 0
                        else f" && {self.visit(gen_if)} "
                    )
            gen_exp.append(filter_str)

        return "".join(gen_exp)

    def visit_Global(self, node) -> str:
        return "//global {0}".format(", ".join(node.names))

    def visit_Starred(self, node) -> str:
        return "starred!({0})/*unsupported*/".format(self.visit(node.value))

    def visit_IfExp(self, node) -> str:
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"{test} ? ({body}) : ({orelse})"
