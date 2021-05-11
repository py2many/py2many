import ast
import functools
import textwrap

from .clike import CLikeTranspiler
from .declaration_extractor import DeclarationExtractor
from py2many.tracer import is_list, defined_before, is_class_or_module, is_self_arg

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.inference import get_inferred_type

from typing import Optional, List


class DartIntegerDivRewriter(ast.NodeTransformer):
    def visit_BinOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.Div):
            left_type = get_id(get_inferred_type(node.left))
            right_type = get_id(get_inferred_type(node.right))
            if set([left_type, right_type]) == {"int"}:
                # This attribute should technically be on node.op
                # But python seems to use the same AST node for other
                # division operations?
                node.use_integer_div = True
        return node


class DartTranspiler(CLikeTranspiler):
    NAME = "dart"

    CONTAINER_TYPE_MAP = {
        "List": "List",
        "Dict": "Map",
        "Set": "Set",
        "Optional": "Nothing",
    }

    def __init__(self):
        super().__init__()
        self._container_type_map = self.CONTAINER_TYPE_MAP
        self._default_type = "var"
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        return f"__tmp{self._temp}"

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"import '{mod}';" for mod in usings)
        return f"// @dart=2.9\n{uses}" if uses else ""

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
            args_list.append(f"{typename} {arg}")

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                return_type = f"{typename}"
            else:
                return_type = "RT"
                typedecls.append("RT")

        template = ""
        if len(typedecls) > 0:
            template = "<{0}>".format(", ".join(typedecls))

        args = ", ".join(args_list)
        funcdef = f"{return_type} {node.name}{template}({args}) {{"
        return funcdef + "\n" + body + "}\n\n"

    def visit_Return(self, node):
        if node.value:
            return "return {0};".format(self.visit(node.value))
        return "return;"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Lambda(self, node):
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return f"({args_string}) => {body}"

    def visit_Attribute(self, node):
        attr = node.attr

        value_id = self.visit(node.value)

        if is_list(node.value):
            if node.attr == "append":
                attr = "add"
        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_self_arg(value_id, node.scopes):
            return attr

        return f"{value_id}.{attr}"

    def visit_range(self, node, vargs: List[str]) -> str:
        start = 0
        step = 1
        if len(vargs) == 1:
            end = vargs[0]
        elif len(node.args) == 2:
            start = vargs[0]
            end = vargs[1]
        elif len(node.args) == 3:
            start = vargs[0]
            end = vargs[1]
            step = vargs[2]
        else:
            raise Exception(
                "encountered range() call with unknown parameters: range({})".format(
                    vargs
                )
            )

        return f"([for(var i = {start}; i < {end}; i += {step}) i])"

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("%s")
        self._usings.add("package:sprintf/sprintf.dart")
        placeholders_str = " ".join(placeholders)
        vargs_str = ", ".join(vargs)
        return rf'print(sprintf("{placeholders_str}", [{vargs_str}]))'

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
            self._usings.add("dart:math")
            vargs_str = ", ".join(vargs)
            return f"{min_max}({vargs_str})"

        # small one liners are inlined here as lambdas
        small_dispatch_map = {
            "int": lambda: f"{vargs[0]}.toInt()",
            "str": lambda: f"{vargs[0]}.toString()",
            "len": lambda: f"{vargs[0]}.length",
            "floor": lambda: f"{vargs[0]}.floor()",
            "max": functools.partial(visit_min_max, is_max=True),
            "min": functools.partial(visit_min_max, is_min=True),
        }

        if fname in small_dispatch_map:
            return small_dispatch_map[fname]()
        return None

    def visit_Call(self, node):
        fname = self.visit(node.func)
        vargs = []

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
        return f"{fname}({args})"

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for (final {0} in {1}) {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Str(self, node):
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node):
        bytes_str = "{0}".format(node.s)
        return bytes_str.replace("'", '"')  # replace single quote with double quote

    def visit_Compare(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        if isinstance(node.ops[0], ast.In):
            return "{0}.contains({1})".format(right, left)
        elif isinstance(node.ops[0], ast.NotIn):
            return "!({0}.contains({1}))".format(right, left)

        return super().visit_Compare(node)

    def visit_Name(self, node):
        exception_name_map = {"ZeroDivisionError": "IntegerDivisionByZeroException"}
        if node.id == "None":
            return "null"
        elif node.id in exception_name_map:
            return exception_name_map[node.id]
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node):
        if node.value is None:
            return "null"
        else:
            return super().visit_NameConstant(node)

    def _make_block(self, node):
        buf = []
        buf.append("{")
        buf.extend([self.visit(child) for child in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        var_definitions = []
        for cv in node.common_vars:
            typename = "var"
            if hasattr(cv, "annotation"):
                typename = get_id(cv.annotation)

            var_definitions.append((typename, cv))
        decls = "\n".join([f"{typename} {cv};" for typename, cv in var_definitions])

        return decls + "\n\n" + super().visit_If(node)

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
            return "std::vector ({0},{1})".format(
                self.visit(node.right), self.visit(node.left.elts[0])
            )
        else:
            return super().visit_BinOp(node)

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(DartTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments

        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        fields = []
        index = 0
        constructor = ""
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append(f"{typename} {declaration};")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        fields = "\n".join(fields)
        body = [self.visit(b) for b in node.body]
        if node.is_dataclass:
            args = [arg for arg in declarations.keys()]
            args = ", ".join([f"this.{arg}" for arg in args])
            constructor = f"{node.name}({args}) {{}}"
            body = [constructor] + body
        body = "\n".join(body)

        return f"class {node.name} {{\n{fields}\n\n {body}\n}}\n"

    def visit_IntEnum(self, node):
        # TODO: Consider using Vnum instead of the language built-in
        # Any python enum which specifies a non default value will break this
        fields = []
        for member, var in node.class_assignments.items():
            var = self.visit(var)
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join(fields)
        return f"enum {node.name} {{\n{fields}\n}}\n\n"

    def visit_StrEnum(self, node):
        # TODO: Dedup with other enum implementations
        self._usings.add("package:vnum/vnum.dart")
        fields = []
        ename = node.name
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = f'"{member}"'
            fields.append(
                f"            static final {member} = const {ename}.define({var});"
            )
        fields = "\n".join(["    " * 2 + f for f in fields])
        return textwrap.dedent(
            f"""\
            @VnumDefinition
            class {node.name} extends Vnum<String> {{\n{fields}

            const {node.name}.define(String fromValue) : super.define(fromValue);
              factory {node.name}(String value) => Vnum.fromValue(value, {node.name});
            }}
            """
        )

    def visit_IntFlag(self, node):
        self._usings.add("package:vnum/vnum.dart")
        fields = []
        ename = node.name
        for i, (member, var) in enumerate(node.class_assignments.items()):
            var = self.visit(var)
            if var == "auto()":
                var = i
            fields.append(
                f"            static final {member} = const {ename}.define({var});"
            )
        fields = "\n".join(["    " * 2 + f for f in fields])
        return textwrap.dedent(
            f"""\
            @VnumDefinition
            class {node.name} extends Vnum<int> {{\n{fields}

            const {node.name}.define(int fromValue) : super.define(fromValue);
              factory {node.name}(int value) => Vnum.fromValue(value, {node.name});
            }}
            """
        )

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
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            return "[{0}]".format(", ".join(elements))

        else:
            return "[]"

    def visit_Dict(self, node):
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{k} : {v}" for k, v in zip(keys, values)])
        return f"{{{kv_pairs}}}"

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

    def visit_Raise(self, node):
        exc = self.visit(node.exc)
        return f"throw new {exc};"

    def visit_Try(self, node):
        buf = []
        buf.append("try {")
        buf.extend([self.visit(child) for child in node.body])
        buf.append("}")

        for handler in node.handlers:
            buf.append(self.visit(handler))

        if node.finalbody:
            buf.append("finally {")
            buf.extend([self.visit(child) for child in node.finalbody])
            buf.append("}")

        return "\n".join(buf)

    def visit_ExceptHandler(self, node):
        buf = []
        if node.type:
            type_str = self.visit(node.type)
            catch_str = ""
            if node.name:
                catch_str = f" catch({node.name})"
            buf.append(f"on {type_str}{catch_str} {{")
        else:
            buf.append("catch(e) {")
        buf.extend([self.visit(child) for child in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Assert(self, node):
        condition = self.visit(node.test)
        return f"assert({condition});"

    def visit_AnnAssign(self, node):
        target, type_str, val = super().visit_AnnAssign(node)
        return f"{type_str} {target} = {val};"

    def _visit_AssignOne(self, node, target):
        kw = "var" if is_mutable(node.scopes, get_id(target)) else "final"

        if isinstance(target, ast.Tuple):
            self._usings.add("package:tuple/tuple.dart")
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            value_types = "int, int"
            count = len(elts)
            tmp_var = self._get_temp()
            buf = [f"{kw} {tmp_var} = Tuple{count}<{value_types}>{value};"]
            for i, elt in enumerate(elts):
                buf.extend([f"{elt} = {tmp_var}.item{i+1};"])
            return "\n".join(buf)

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return f"{kw} {target_id} = {value};"

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value};"

        definition = node.scopes.find(target.id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value};"
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            elements = ", ".join(elements)
            target = self.visit(target)

            return f"{kw} {target} = [{elements}];"
        else:
            typename = self._typename_from_annotation(target)
            target = self.visit(target)
            value = self.visit(node.value)

            if typename != self._default_type:
                if kw == self._default_type:
                    return f"{typename} {target} = {value};"
            else:
                return f"{kw} {target} = {value};"

            return f"{kw} {typename} {target} = {value};"

    def visit_Delete(self, node):
        target = node.targets[0]
        return "{0}.drop()".format(self.visit(target))

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
        return "await!({0})".format(self.visit(node.value))

    def visit_AsyncFunctionDef(self, node):
        return "#[async]\n{0}".format(self.visit_FunctionDef(node))

    def visit_Yield(self, node):
        return "//yield is unimplemented"

    def visit_Print(self, node):
        buf = []
        for n in node.values:
            value = self.visit(n)
            buf.append('println("{{:?}}",{0})'.format(value))
        return "\n".join(buf)

    def visit_DictComp(self, node):
        return "DictComp /*unimplemented()*/"

    def visit_GeneratorExp(self, node):
        elt = self.visit(node.elt)
        generator = node.generators[0]
        target = self.visit(generator.target)
        iter = self.visit(generator.iter)

        # HACK for dictionary iterators to work
        if not iter.endswith("keys()") or iter.endswith("values()"):
            iter += ".iter()"

        map_str = ".map(|{0}| {1})".format(target, elt)
        filter_str = ""
        if generator.ifs:
            filter_str = ".cloned().filter(|&{0}| {1})".format(
                target, self.visit(generator.ifs[0])
            )

        return "{0}{1}{2}.collect::<Vec<_>>()".format(iter, filter_str, map_str)

    def visit_ListComp(self, node):
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_Global(self, node):
        return "//global {0}".format(", ".join(node.names))

    def visit_Starred(self, node):
        return "starred!({0})/*unsupported*/".format(self.visit(node.value))

    def visit_Set(self, node):
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"new Set.from([{elements_str}])"

    def visit_IfExp(self, node):
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"{test}? ({body}) : ({orelse})"
