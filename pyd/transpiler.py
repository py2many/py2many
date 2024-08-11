import ast
import textwrap
from typing import List

from py2many.analysis import get_id, is_void_function  # , is_mutable
from py2many.clike import class_for_typename
from py2many.declaration_extractor import DeclarationExtractor
from py2many.inference import get_inferred_type
from py2many.tracer import defined_before, is_class_or_module, is_list, is_self_arg

from .clike import CLikeTranspiler
from .plugins import (
    ATTR_DISPATCH_TABLE,
    CLASS_DISPATCH_TABLE,
    DISPATCH_MAP,
    FUNC_DISPATCH_TABLE,
    MODULE_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)


class DIntegerDivRewriter(ast.NodeTransformer):
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


class DTranspiler(CLikeTranspiler):
    NAME = "d"

    CONTAINER_TYPE_MAP = {
        "List": "[]",
        "Dict": "Map",
        "Set": "auto",  # RedBlackTree
        "Optional": "Nothing",
    }

    def __init__(self):
        super().__init__()
        self._container_type_map = self.CONTAINER_TYPE_MAP
        self._default_type = "auto"
        self._temp = 0
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        self._main_signature_arg_names = ["argv"]
        self._classes = set()

    def _get_temp(self):
        self._temp += 1
        return f"__tmp{self._temp}"

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"import {mod};" for mod in usings)
        return f"// generated by py2many --dlang=1\n{uses}" if uses else ""

    # main(`string[]` argv)
    def _combine_value_index(self, value_type, index_type) -> str:
        # print(value_type, index_type)
        # [] string => `string[]`
        # [] ['string', 'int'] => `int[string]`
        # [] string, int => `int[string]`
        if value_type == "Map" and ", " in index_type:
            its = index_type.split(",")
            return f"{its[1]}[{its[0]}]"
        return f"{index_type}{value_type}"

    def visit_FunctionDef(self, node) -> str:
        body = "\n".join([self.visit(n) for n in node.body])
        typenames, args = self.visit(node.args)

        args_list = []
        if len(args) and hasattr(node, "self_type"):
            # implicit this
            del typenames[0]
            del args[0]

        is_python_main = getattr(node, "python_main", False)

        typedecls = []
        index = 0
        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            if is_python_main and arg == "argc":
                continue

            if typename == "T":
                typename = "T{0}".format(index)
                typedecls.append(typename)
                index += 1
            args_list.append(f"{typename} {arg}")

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                typename = self._typename_from_annotation(node, attr="returns")
                if typename != self._default_type:
                    return_type = f"{typename}"
            if not return_type:
                return_type = "RT"
                typedecls.append("RT")
        else:
            return_type = "void"

        template = ""
        if len(typedecls) > 0:
            template = "({0})".format(", ".join(typedecls))

        args = ", ".join(args_list)
        funcdef = f"{return_type} {node.name}{template}({args}) {{"
        return funcdef + "\n" + body + "}\n\n"

    def visit_Return(self, node) -> str:
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

    def visit_Lambda(self, node) -> str:
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return f"({args_string}) => {body}"

    def visit_Attribute(self, node) -> str:
        attr = node.attr

        value_id = self.visit(node.value)

        if value_id == "sys":
            if attr == "argv":
                return "argv"
            elif attr in ["stderr", "stdin", "stdout"]:
                self._usings.add("std.stdio")
                return attr

        if is_list(node.value):
            if node.attr == "append":
                # list.append method return None
                return f"{value_id} ~= "

        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_self_arg(value_id, node.scopes):
            return attr

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
        if vargs:
            args = ", ".join(vargs)
        else:
            args = ""

        new = "new " if fname in self._classes else ""

        return f"{new}{fname}({args})"

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("foreach ({0}; {1}) {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Str(self, node) -> str:
        return "" + super().visit_Str(node) + ""

    def visit_Bytes(self, node) -> str:
        bytes_str = "{0}".format(node.s)
        return bytes_str.replace("'", '"')  # replace single quote with double quote

    def visit_Compare(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        type_is_set = False
        if hasattr(node.comparators[0], "annotation"):
            self._generic_typename_from_annotation(node.comparators[0])
            value_type = getattr(
                node.comparators[0].annotation, "generic_container_type", None
            )
            if value_type:
                if value_type[0] == "Dict":
                    right += ".keys"
                if value_type[0] == "Set":
                    type_is_set = True

        if right.endswith(".keys()") or right.endswith(".values()"):
            right = right[:-2]

        def _gen_in():
            if type_is_set:
                return "{1} in {0}".format(right, left)
            else:
                self._usings.add("std.algorithm")
                return "{0}.canFind({1})".format(right, left)

        if isinstance(node.ops[0], ast.In):
            return _gen_in()
        elif isinstance(node.ops[0], ast.NotIn):
            return "!({_gen_in()})"
        elif isinstance(node.ops[0], ast.Eq):
            if hasattr(node.left, "annotation"):
                self._generic_typename_from_annotation(node.left)
                value_type = getattr(
                    node.left.annotation, "generic_container_type", None
                )
                if value_type and value_type[0] == "List":
                    self._usings.add("std.algorithm : equal")
                    return f"equal({left}, {right})"

        return super().visit_Compare(node)

    def visit_Constant(self, node) -> str:
        if isinstance(node.value, complex):
            str_value = str(node.value)
            return "std.complex.complex(0, %s)" % (
                str_value.replace("j", "") if str_value.endswith("j") else str_value
            )
        else:
            return super().visit_Constant(node)

    def visit_Name(self, node) -> str:
        exception_name_map = {"ZeroDivisionError": "IntegerDivisionByZeroException"}
        if node.id == "None":
            return "null"
        elif node.id in exception_name_map:
            return exception_name_map[node.id]
        else:
            return super().visit_Name(node)

    def visit_NameConstant(self, node) -> str:
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

    def visit_If(self, node) -> str:
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        var_definitions = []
        for cv in node.common_vars:
            typename = "auto"
            if hasattr(cv, "annotation"):
                typename = get_id(cv.annotation)

            var_definitions.append((typename, cv))
        decls = "\n".join([f"{typename} {cv};" for typename, cv in var_definitions])

        decls = ""  # TODO: we need to check if cv is defined in the outer-scope already
        return decls + "\n\n" + super().visit_If(node)

    def visit_UnaryOp(self, node) -> str:
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super().visit_UnaryOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(DTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments

        ret = super().visit_ClassDef(node)
        self._classes.add(node.name)
        if ret is not None:
            return ret

        decorators = [get_id(d) for d in node.decorator_list]
        decorators = [
            class_for_typename(t, None, self._imported_names) for t in decorators
        ]
        for d in decorators:
            if d in CLASS_DISPATCH_TABLE:
                ret = CLASS_DISPATCH_TABLE[d](self, node)
                if ret is not None:
                    return ret

        raw_fields = []
        index = 0
        constructor = ""
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            raw_fields.append(f"{typename} {declaration}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        fields = ";\n".join(raw_fields) + ";\n"
        body = [self.visit(b) for b in node.body]
        if node.is_dataclass:
            args = [arg for arg in declarations.keys()]
            sets = "\n".join([f"this.{arg} = {arg};" for arg in args])
            args = ", ".join(raw_fields)
            constructor = f"this({args}) {{{sets}}}"
            body = [constructor] + body
        body = "\n".join(body)

        return f"class {node.name} {{\n{fields}\n\n {body}\n}}\n"

    def visit_IntEnum(self, node) -> str:
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

    def visit_StrEnum(self, node) -> str:
        # TODO: Dedup with other enum implementations
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

    def visit_IntFlag(self, node) -> str:
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

    def _import(self, name: str) -> str:
        return f'import "{name}";'

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if len(names) == 1:
            # TODO: make this more generic so it works for len(names) > 1
            name = names[0]
            lookup = f"{module_name}.{name}"
            if lookup in MODULE_DISPATCH_TABLE:
                dlang_module_name, dlang_name = MODULE_DISPATCH_TABLE[lookup]
                return f"import {dlang_module_name};  // {dlang_name}"
        names = ", ".join(names)
        return f'import "{module_name}";  // {names}'

    def visit_List(self, node) -> str:
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            return "[{0}]".format(", ".join(elements))  # the list content

        else:
            return "[]"

    def visit_Dict(self, node) -> str:
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(k) for k in node.values]
        kv_pairs = ", ".join([f"{k} : {v}" for k, v in zip(keys, values)])
        return f"[{kv_pairs}]"  # the dict content

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in self.CONTAINER_TYPE_MAP:
                value = self.CONTAINER_TYPE_MAP[value]
            if value == "Tuple":
                return "({0})".format(index)
            return "{0}[{1}]".format(value, index)
        if getattr(node, "lhs", False):
            return "{0}[{1}]".format(value, index)
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

    def visit_Delete(self, node) -> str:
        self._usings.add("core.memory")
        target = node.targets[0]
        target_str = self.visit(target)
        return (
            f"destroy!true({target_str}); core.memory.GC.free(cast(void*){target_str});"
        )

    def visit_Raise(self, node) -> str:
        if node.exc is not None:
            return "throw new {};".format(self.visit(node.exc))
        return "throw new Exception();"

    def visit_Try(self, node) -> str:
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

    def visit_ExceptHandler(self, node) -> str:
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

    def visit_Assert(self, node) -> str:
        condition = self.visit(node.test)
        return f"assert({condition});"

    def is_const_var(self, target) -> bool:
        var = get_id(target)
        return (var is not None) and (var.isupper())

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        if self.is_const_var(target):
            type_str = "const " + type_str
        return f"{type_str} {target} = {val};"

    def _visit_AssignOne(self, node, target) -> str:
        kw = "auto"  # if is_mutable(node.scopes, get_id(target)) else "final"  # TODO(no const in Python)
        if self.is_const_var(target):
            kw = "const"
        # need to check var is defined in the outer-scope already
        definition = node.scopes.parent_scopes.find(get_id(target))
        if definition is not None:
            kw = ""

        if isinstance(target, ast.Tuple):
            self._usings.add("std.typecons : tuple")
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            tmp_var = self._get_temp()
            buf = [
                f"auto {tmp_var} = tuple{value};"
            ]  # NOTE: tmp_var is always `auto` here in Dlang.
            for i, elt in enumerate(elts):
                buf.extend([f"{elt} = {tmp_var}[{i}];"])
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

        if definition is None:
            definition = node.scopes.find(get_id(target))
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return f"{target} = {value};"
        else:
            typename = self._typename_from_annotation(target)
            target = self.visit(target)
            value = self.visit(node.value)

            if typename == "complex":
                self._usings.add("std.complex")
                typename = "auto"

            if typename != self._default_type:
                if kw == self._default_type:
                    return f"{typename} {target} = {value};"
            else:
                return f"{kw} {target} = {value};"

            return f"{kw} {typename} {target} = {value};"

    def visit_Print(self, node) -> str:
        buf = []
        for n in node.values:
            value = self.visit(n)
            buf.append('println("{{:?}}",{0})'.format(value))
        return "\n".join(buf)

    def visit_GeneratorExp(self, node) -> str:
        elt = self.visit(node.elt)
        generator = node.generators[0]
        target = self.visit(generator.target)
        iter = self.visit(generator.iter)

        # HACK for dictionary iterators to work
        """
        if not iter.endswith("keys()") or iter.endswith("values()"):
            iter += ".iter()"
        """

        self._usings.add("std.algorithm")
        self._usings.add("std.array")
        map_str = ".map!({0} => {1})".format(target, elt)
        filter_str = ""
        if generator.ifs:
            filter_str = ".cloned().filter(|&{0}| {1})".format(
                target, self.visit(generator.ifs[0])
            )

        return "{0}{1}{2}.array()".format(iter, filter_str, map_str)

    def visit_ListComp(self, node) -> str:
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_Global(self, node) -> str:
        return "//global {0}".format(", ".join(node.names))

    def visit_Starred(self, node) -> str:
        return "starred!({0})/*unsupported*/".format(self.visit(node.value))

    def visit_Set(self, node) -> str:
        elements = [self.visit(e) for e in node.elts]
        elements_str = ", ".join(elements)
        return f"redBlackTree([{elements_str}])"

    def visit_IfExp(self, node) -> str:
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"{test}? ({body}) : ({orelse})"
