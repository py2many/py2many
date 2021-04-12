import ast

from .clike import CLikeTranspiler
from py2many.declaration_extractor import DeclarationExtractor
from py2many.tracer import (
    is_list,
    defined_before,
    is_class_or_module,
)

from py2many.scope import add_scope_context
from py2many.annotation_transformer import add_annotation_flags
from py2many.mutability_transformer import detect_mutable_vars
from py2many.context import add_variable_context, add_list_calls
from py2many.analysis import add_imports, is_void_function, get_id, is_mutable
from typing import Optional, List

container_types = {
    "List": "openArray",
    "Dict": "Table",
    "Set": "set",
    "Optional": "Option",
}


def transpile(source):
    """
    Transpile a single python translation unit (a python script) into
    Nim code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    add_annotation_flags(tree)
    add_imports(tree)

    transpiler = NimTranspiler()

    return transpiler.visit(tree)


class NimTranspiler(CLikeTranspiler):
    def __init__(self, indent=2):
        super().__init__()
        self._headers = set([])
        self._indent = " " * indent

    def indent(self, code, level=1):
        return self._indent * level + code

    def visit_FunctionDef(self, node):
        body = "\n".join([self.indent(self.visit(n)) for n in node.body])
        typenames, args = self.visit(node.args)

        args_list = []
        if len(args) and hasattr(node, "self_type"):
            typenames[0] = node.self_type

        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            args_list.append(f"{arg}: {typename}".format(arg, typename))

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                return_type = ": {0}".format(self.visit(node.returns))
            else:
                return_type = ""

        args = ", ".join(args_list)
        funcdef = f"proc {node.name}({args}){return_type} ="
        return f"{funcdef}\n{body}\n"

    def visit_Return(self, node):
        if node.value:
            return "return {0}".format(self.visit(node.value))
        return "return"

    def visit_arguments(self, node):
        args = [self.visit(arg) for arg in node.args]

        # switch to zip
        types = []
        names = []
        for arg in args:
            types.append(arg[0])
            names.append(arg[1])

        return types, names

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "T"
        if node.annotation:
            typename = self.visit(node.annotation)
        return (typename, id)

    def visit_Lambda(self, node):
        _, args = self.visit(node.args)
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return "|{0}| {1}".format(args_string, body)

    def visit_Attribute(self, node):
        attr = node.attr

        value_id = self.visit(node.value)

        if is_list(node.value):
            if node.attr == "append":
                attr = "push"
        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return "{0}::{1}".format(value_id, attr)

        return value_id + "." + attr

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return "0..{}".format(vargs[0])
        elif len(node.args) == 2:
            return "{}..{}".format(vargs[0], vargs[1])
        elif len(node.args) == 3:
            return "countup({},{},{}".format(vargs[0], vargs[1], vargs[2])

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        return f"echo {args}"

    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        dispatch_map = {
            "range": self.visit_range,
            "xrange": self.visit_range,
            "print": self.visit_print,
        }

        if fname in dispatch_map:
            return dispatch_map[fname](node, vargs)

        # small one liners are inlined here as lambdas
        small_dispatch_map = {"str": lambda: f"$({vargs[0]})"}
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
        buf.append(f"for {target} in {it}:")
        buf.extend(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        return "\n".join(buf)

    def visit_While(self, node):
        buf = []
        buf.append("while {0}:".format(self.visit(node.test)))
        buf.extend(
            [self.indent(self.visit(n), level=node.level + 1) for n in node.body]
        )
        return "\n".join(buf)

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_Str(self, node):
        return "" + super(NimTranspiler, self).visit_Str(node) + ""

    def visit_Bytes(self, node):
        bytes_str = "{0}".format(node.s)
        return bytes_str.replace("'", '"')  # replace single quote with double quote

    def visit_Compare(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        if isinstance(node.ops[0], ast.In):
            return "{0}.iter().any(|&x| x == {1})".format(
                right, left
            )  # is it too much?
        elif isinstance(node.ops[0], ast.NotIn):
            return "{0}.iter().all(|&x| x != {1})".format(
                right, left
            )  # is it even more?

        return super(NimTranspiler, self).visit_Compare(node)

    def visit_Name(self, node):
        if node.id == "None":
            return "None"
        else:
            return super(NimTranspiler, self).visit_Name(node)

    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "None"
        else:
            return super(NimTranspiler, self).visit_NameConstant(node)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        # HACK to determine if main function name is visited
        if self.visit(node.test) == '__name__ == "__main__"':
            buf = ["proc main() ="]
            buf.extend([self.indent(self.visit(child)) for child in node.body])
            buf.append("")
            buf.append("main()")
            return "\n".join(buf)
        body = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.body
            ]
        )
        orelse = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.orelse
            ]
        )
        test = self.visit(node.test)
        if node.orelse:
            orelse = self.indent(f"else:\n{orelse}", level=node.level)
        else:
            orelse = ""
        return f"if {test}:\n{body}\n{orelse}"

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super(NimTranspiler, self).visit_UnaryOp(node)

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
            return super(NimTranspiler, self).visit_BinOp(node)

    def visit_Module(self, node):
        buf = []
        for header in self._headers:
            buf.append(header)
        buf += [self.visit(b) for b in node.body]
        return "\n".join(buf)

    def visit_ClassDef(self, node):
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret
        extractor = DeclarationExtractor(NimTranspiler())
        extractor.visit(node)
        declarations = extractor.get_declarations()

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append(f"{declaration}: {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        object_def = "type\n"
        object_def += self.indent(f"{node.name} = object\n", level=node.level + 1)
        object_def += "\n".join([self.indent(f, level=node.level + 2) for f in fields])
        body = [self.visit(b) for b in node.body]
        body = "\n".join(body)
        return f"{object_def}\n{body}\n"

    def visit_IntEnum(self, node):
        extractor = DeclarationExtractor(NimTranspiler())
        extractor.visit(node)

        fields = []
        for member, var in extractor.class_assignments.items():
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join([self.indent(f) for f in fields])
        return f"type {node.name} = enum\n{fields}\n\n"

    def visit_IntFlag(self, node):
        extractor = DeclarationExtractor(NimTranspiler())
        extractor.visit(node)

        fields = []
        for member, var in extractor.class_assignments.items():
            if var == "auto()":
                fields.append(f"{member},")
            else:
                fields.append(f"{member} = {var},")
        fields = "\n".join([self.indent(f, level=2) for f in fields])
        flags = self.indent(f"{node.name}Flags = set[{node.name}]")
        return "\n".join(
            ["type", self.indent(f"{node.name} = enum"), f"{fields}", f"{flags}", ""]
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
            elements = ", ".join(elements)
            return f"@[{elements}]"
        else:
            return "[]"

    def visit_Dict(self, node):
        if len(node.keys) > 0:
            kv_string = []
            for i in range(len(node.keys)):
                key = self.visit(node.keys[i])
                value = self.visit(node.values[i])
                kv_string.append("({0}, {1})".format(key, value))
            initialization = "[{0}].iter().cloned().collect::<HashMap<_,_>>()"
            return initialization.format(", ".join(kv_string))
        else:
            return "HashMap::new()"

    def visit_Subscript(self, node):
        value = self.visit(node.value)
        index = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in container_types:
                value = container_types[value]
            if value == "Tuple":
                return f"({index})"
            return f"{value}[{index}]"
        return f"{value}[{index}]"

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

    def visit_Elipsis(self, node):
        return "compile_error!('Elipsis is not supported');"

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
        return "assert({0})".format(self.visit(node.test))

    def visit_AnnAssign(self, node):
        target = self.visit(node.target)
        type_str = self.visit(node.annotation)
        val = self.visit(node.value)
        return "{0}::{1} = {2}".format(target, type_str, val)

    def visit_Assign(self, node):
        target = node.targets[0]

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

        definition = node.scopes.find(target.id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            elements = ", ".join(elements)
            target = self.visit(target)
            return f"{target} = @[{elements}]"
        else:
            mutable = False
            if is_mutable(node.scopes, get_id(target)):
                mutable = True

            target = self.visit(target)
            value = self.visit(node.value)

            if len(node.scopes) == 1:
                if isinstance(
                    node.scopes[0], ast.Module
                ):  # if assignment is module level it must be const
                    return f"const {target} = {value};"
            kw = "var" if mutable else "let"
            return f"{kw} {target} = {value}"

    def visit_Delete(self, node):
        target = node.targets[0]
        return "{0}.drop()".format(self.visit(target))

    def visit_Raise(self, node):
        if node.exc is not None:
            return "raise!({0}); //unsupported".format(self.visit(node.exc))
        # This handles the case where `raise` is used without
        # specifying the exception.
        return "raise!(); //unsupported"

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
        value = self.visit(node.value)
        return f"yield {value}"

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
        elts = []
        for i in range(len(node.elts)):
            elt = self.visit(node.elts[i])
            elts.append(elt)

        if elts:
            initialization = "[{0}].iter().cloned().collect::<HashSet<_>>()"
            return initialization.format(", ".join(elts))
        else:
            return "HashSet::new()"

    def visit_IfExp(self, node):
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        test = self.visit(node.test)
        return f"""
if {test}:
    {body}
else:
    {orelse}
"""
