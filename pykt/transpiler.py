import ast
import functools
import re

from .clike import CLikeTranspiler
from .declaration_extractor import DeclarationExtractor
from .inference import get_inferred_kotlin_type
from py2many.tracer import is_list, defined_before, is_class_or_module, is_self_arg

from py2many.analysis import get_id, is_mutable, is_void_function
from typing import Optional, List, Tuple


class KotlinPrintRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        return f"__tmp{self._temp}"

    def visit_Call(self, node):
        fname = self.visit(node.func)
        if (
            get_id(fname) == "print"
            and len(node.args) == 1
            and not (
                isinstance(node.args[0], ast.Name)
                or isinstance(node.args[0], ast.Constant)
            )
        ):
            tmp = ast.Name(id=self._get_temp(), lineno=node.lineno)
            ret = ast.If(
                test=ast.Constant(value=True),
                body=[
                    ast.Assign(targets=[tmp], value=node.args[0], lineno=node.lineno),
                    node,
                ],
                orelse=[],
                lineno=node.lineno,
            )
            node.args[0] = tmp
            return ret

        return node


class KotlinTranspiler(CLikeTranspiler):
    NAME = "kotlin"

    CONTAINER_TYPE_MAP = {
        "List": "Array",
        "Dict": "Dict",
        "Set": "Set",
        "Optional": "Nothing",
    }

    def __init__(self):
        super().__init__()
        self._default_type = "var"
        self._container_type_map = self.CONTAINER_TYPE_MAP

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"import {mod}" for mod in usings)
        return uses

    def visit_FunctionDef(self, node):
        body = "\n".join([self.visit(n) for n in node.body])
        typenames, args = self.visit(node.args)

        args_list = []
        if len(args) and hasattr(node, "self_type"):
            # implicit this
            del typenames[0]
            del args[0]

        typedecls = []
        index = 0
        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            if typename == "T":
                typename = "T{0}".format(index)
                typedecls.append(typename)
                index += 1
            args_list.append(f"{arg}: {typename}")

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                return_type = f": {typename}"
            else:
                return_type = ": RT"
                typedecls.append("RT")

        template = ""
        if len(typedecls) > 0:
            template = "<{0}>".format(", ".join(typedecls))

        args = ", ".join(args_list)
        funcdef = f"fun {node.name}{template}({args}){return_type} {{"
        return funcdef + "\n" + body + "}\n\n"

    def visit_Return(self, node):
        if node.value:
            ret = self.visit(node.value)
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                return_type = self._typename_from_annotation(fndef, attr="returns")
                value_type = get_inferred_kotlin_type(node.value)
                if return_type != value_type and value_type is not None:
                    return f"return {ret} as {return_type}"
            return f"return {ret}"
        return "return"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        id, _ = self._check_keyword(id)
        typename = "T"
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Lambda(self, node):
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return f"{{ {args_string} -> {body} }}"

    def visit_Attribute(self, node):
        attr = node.attr

        value_id = self.visit(node.value)

        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_self_arg(value_id, node.scopes):
            return attr

        return f"{value_id}.{attr}"

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return "(0..{}-1)".format(vargs[0])
        elif len(node.args) == 2:
            return "({}..{}-1)".format(vargs[0], vargs[1])
        elif len(node.args) == 3:
            return "({}..{}-1 step {})".format(vargs[0], vargs[1], vargs[2])

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        def _format(arg):
            if arg.isdigit():
                return arg
            if re.match(r"'.*'", arg) or re.match(r'".*"', arg):
                return arg[1:-1]
            else:
                return f"${arg}"

        vargs_str = " ".join([f"{_format(arg)}" for arg in vargs])
        return f'println("{vargs_str}")'

    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        dispatch_map = {
            "range": self.visit_range,
            "xrange": self.visit_range,
            "print": self.visit_print,
        }

        if fname in dispatch_map:
            return dispatch_map[fname](node, vargs)

        def visit_min_max(is_max: bool) -> str:
            min_max = "max" if is_max else "min"
            self._usings.add(f"kotlin.math.{min_max}")
            self._typename_from_annotation(node.args[0])
            if hasattr(node.args[0], "container_type"):
                return f"maxOf({vargs[0]})"
            else:
                all_vargs = ", ".join(vargs)
                return f"{min_max}({all_vargs})"

        def visit_floor():
            self._usings.add("kotlin.math.floor")
            return f"floor({vargs[0]}).toInt()"

        # small one liners are inlined here as lambdas
        small_dispatch_map = {
            "int": lambda: f"{vargs[0]}.toInt()",
            "str": lambda: f"{vargs[0]}.toString()",
            # TODO: strings use .length
            "len": lambda: f"{vargs[0]}.size",
            "max": functools.partial(visit_min_max, is_max=True),
            "min": functools.partial(visit_min_max, is_min=True),
            "floor": visit_floor,
            "reversed": lambda: f"{vargs[0]}.reversed()",
        }
        if fname in small_dispatch_map:
            return small_dispatch_map[fname]()
        return None

    def visit_Call(self, node):
        fname = self.visit(node.func)
        vargs = []

        if (
            hasattr(node.func, "value")
            and is_list(node.func.value)
            and fname.endswith(".append")
        ):
            fname = fname.replace(".append", " +=")

        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret
        if vargs:
            args = ", ".join(vargs)
        else:
            args = ""

        if fname.endswith("+="):
            return f"{fname} {args}"

        return f"{fname}({args})"

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for ({0} in {1}) {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Str(self, node):
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node):
        bytes_str = "{0}".format(node.s)
        return bytes_str.replace("'", '"')  # replace single quote with double quote

    def visit_Name(self, node):
        if node.id == "None":
            return "None"
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node):
        if node.value is None:
            return "null"
        else:
            return super().visit_NameConstant(node)

    def _make_block(self, node):
        buf = []
        buf.append("if (true) {")
        buf.extend([self.visit(child) for child in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)
        return super().visit_If(node)

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super().visit_UnaryOp(node)

    def visit_BinOp(self, node):
        if (
            isinstance(node.left, ast.List)
            and isinstance(node.op, ast.Mult)
            and isinstance(node.right, ast.Num)
        ):
            num = self.visit(node.right)
            elt = self.visit(node.left.elts[0])
            return f"Array({num}) {{ {elt} }}"
        else:
            return super().visit_BinOp(node)

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(KotlinTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            mut = is_mutable(node.scopes, get_id(declaration))
            mut = "var" if mut else "val"
            fields.append(f"{mut} {declaration}: {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        if node.is_dataclass:
            fields = ", ".join(fields)
            body = [self.visit(b) for b in node.body]
            body = "\n".join(body)
            return f"data class {node.name}({fields}) {{\n{body}\n}}\n"
        else:
            fields = "\n".join(fields)
            body = [self.visit(b) for b in node.body]
            body = "\n".join(body)
            return f"class {node.name} {{\n{fields}\n\n {body}\n}}\n"

    def _visit_enum(self, node, typename: str, fields: List[Tuple]):
        fields_list = []

        for field, value in fields:
            fields_list += [
                f"""\
                {field}({value}),
            """
            ]
        fields_str = "".join(fields_list)
        return f"enum class {node.name}(val value: {typename}) {{\n{fields_str}\n}}"

    def visit_StrEnum(self, node):
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = f'"{member}"'
            fields.append((member, var))
        return self._visit_enum(node, "String", fields)

    def visit_IntEnum(self, node):
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = i
            fields.append((member, var))
        return self._visit_enum(node, "Int", fields)

    def visit_IntFlag(self, node):
        fields = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = 1 << i
            fields.append((member, var))
        return self._visit_enum(node, "Int", fields)

    def visit_alias(self, node):
        return "use {0}".format(node.name)

    def visit_Import(self, node):
        imports = [self.visit(n) for n in node.names]
        return "\n".join(i for i in imports if i)

    def visit_ImportFrom(self, node):
        if node.module in self.IGNORED_MODULE_LIST:
            return ""

        names = [n.name for n in node.names]
        names = ", ".join(names)
        module_path = node.module.replace(".", "::")
        return "use {0}::{{{1}}}".format(module_path, names)

    def visit_List(self, node):
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"arrayOf({elements_str})"

    def visit_Set(self, node):
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"setOf({elements_str})"

    def visit_Dict(self, node):
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{k} to {v}" for k, v in zip(keys, values)])
        return f"hashMapOf({kv_pairs})"

    def visit_Subscript(self, node):
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in self.CONTAINER_TYPE_MAP:
                value = self.CONTAINER_TYPE_MAP[value]
            if value == "Tuple":
                return "({0})".format(index)
            return "{0}<{1}>".format(value, index)
        return "{0}[{1}]".format(value, index)

    def visit_Index(self, node):
        return self.visit(node.value)

    def visit_Slice(self, node):
        lower = ""
        if node.lower:
            lower = self.visit(node.lower)
        upper = ""
        if node.upper:
            upper = self.visit(node.upper)

        return "{0}..{1}".format(lower, upper)

    def visit_Tuple(self, node):
        elts = [self.visit(e) for e in node.elts]
        elts = ", ".join(elts)
        if hasattr(node, "is_annotation"):
            return elts
        return "({0})".format(elts)

    def visit_unsupported_body(self, name, body):
        buf = ["let {0} = {{ //unsupported".format(name)]
        buf += [self.visit(n) for n in body]
        buf.append("};")
        return buf

    def visit_Try(self, node, finallybody=None):
        buf = self.visit_unsupported_body("try_dummy", node.body)

        for handler in node.handlers:
            buf += self.visit(handler)
        # buf.append("\n".join(excepts));

        if finallybody:
            buf += self.visit_unsupported_body("finally_dummy", finallybody)

        return "\n".join(buf)

    def visit_ExceptHandler(self, node):
        exception_type = ""
        if node.type:
            exception_type = self.visit(node.type)
        name = "except!({0})".format(exception_type)
        body = self.visit_unsupported_body(name, node.body)
        return body

    def visit_Assert(self, node):
        condition = self.visit(node.test)
        return f"assert({condition})"

    def visit_AnnAssign(self, node):
        target = self.visit(node.target)
        type_str = self._typename_from_annotation(node)
        val = self.visit(node.value) if node.value is not None else None
        if type_str == self._default_type:
            return f"var {target} = {val}"
        return f"var {target}: {type_str} = {val}"

    def _visit_AssignOne(self, node, target):
        kw = "var" if is_mutable(node.scopes, get_id(target)) else "val"

        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            elts_str = ", ".join(elts)
            value = self.visit(node.value)
            if isinstance(node.value, ast.Tuple):
                value = f"Pair{value}"
            return f"{kw} ({elts_str}) = {value}"

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return f"{kw} {target_id} = {value}"

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value}"

        definition = node.scopes.find(target.id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value}"
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            elements = ", ".join(elements)
            target = self.visit(target)

            return f"{kw} {target} = arrayOf({elements})"
        else:
            target = self.visit(target)
            value = self.visit(node.value)

            return f"{kw} {target} = {value}"

    def visit_Delete(self, node):
        target = node.targets[0]
        return "{0}.drop()".format(self.visit(target))

    def visit_Raise(self, node):
        if node.exc is not None:
            exc = self.visit(node.exc)
            return f"throw Exception({exc})"
        return "throw Exception()"

    def visit_With(self, node):
        buf = []

        with_statement = "// with!("
        for i in node.items:
            if i.optional_vars:
                with_statement += "{0} as {1}, ".format(
                    self.visit(i.context_expr), self.visit(i.optional_vars)
                )
            else:
                with_statement += "{0}, ".format(self.visit(i.context_expr))
        with_statement = with_statement[:-2] + ") //unsupported\n{"
        buf.append(with_statement)

        for n in node.body:
            buf.append(self.visit(n))

            buf.append("}")

        return "\n".join(buf)

    def visit_Await(self, node):
        expr = self.visit(node.value)
        return f"{expr}.await()"

    def visit_AsyncFunctionDef(self, node):
        fn = self.visit_FunctionDef(node)
        return f"suspend {fn}"

    def visit_Yield(self, node):
        return "//yield is unimplemented"

    def visit_Print(self, node):
        vargs_str = " ".join([f"${arg}" for arg in node.values])
        return f'println("{vargs_str}")'

    def visit_DictComp(self, node):
        return "DictComp /*unimplemented()*/"

    def visit_GeneratorExp(self, node):
        return "GeneratorExp /*unimplemented()*/"

    def visit_ListComp(self, node):
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_Global(self, node):
        return "//global {0}".format(", ".join(node.names))

    def visit_Starred(self, node):
        return "starred!({0})/*unsupported*/".format(self.visit(node.value))

    def visit_IfExp(self, node):
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"if ({test}) {body} else {orelse}"
