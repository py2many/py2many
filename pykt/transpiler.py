import sys
import ast

from .clike import CLikeTranspiler
from .declaration_extractor import DeclarationExtractor
from py2many.tracer import (
    decltype,
    is_list,
    is_builtin_import,
    defined_before,
    is_class_or_module,
    is_self_arg,
)

from py2many.scope import add_scope_context
from py2many.annotation_transformer import add_annotation_flags
from py2many.mutability_transformer import detect_mutable_vars
from py2many.context import add_variable_context, add_list_calls
from py2many.analysis import add_imports, is_void_function, get_id, is_mutable
from typing import Optional, List

container_types = {"List": "Array", "Dict": "Dict", "Set": "Set", "Optional": "Nothing"}


def transpile(source):
    """
    Transpile a single python translation unit (a python script) into
    Kotlin code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    add_annotation_flags(tree)
    add_imports(tree)

    transpiler = KotlinTranspiler()

    return transpiler.visit(tree)


class KotlinTranspiler(CLikeTranspiler):

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
                return_type = ": {0}".format(self.visit(node.returns))
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
        return f"{{ {args_string} -> {body} }}"

    def visit_Attribute(self, node):
        attr = node.attr

        value_id = self.visit(node.value)

        if is_list(node.value):
            if node.attr == "append":
                attr = "push"
        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return f"{value_id}.{attr}"

        if is_self_arg(value_id, node.scopes):
            return attr

        return f"{value_id}.{attr}"

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return "(0..{})".format(vargs[0])
        elif len(node.args) == 2:
            return "({}..{})".format(vargs[0], vargs[1])
        elif len(node.args) == 3:
            return "({}..{}).step_by({})".format(vargs[0], vargs[1], vargs[2])

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(args)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("%v ")
        self._usings.add("fmt")
        return 'fmt.Printf("{0}\n",{1})'.format(
            "".join(placeholders), ", ".join(values)
        )

    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        dispatch_map = {
            "range": self.visit_range,
            "xrange": self.visit_range,
            "print": self.visit_print,
        }

        if fname in dispatch_map:
            return dispatch_map[fname](node, vargs)

        # small one liners are inlined here as lambdas
        small_dispatch_map = {
            "int": lambda: f"i32::from({vargs[0]})",
            "str": lambda: f"String::from({vargs[0]})",
            "len": lambda: f"{vargs[0]}.len()",
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
        buf.append("for {0} in {1} {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_Str(self, node):
        return "" + super(KotlinTranspiler, self).visit_Str(node) + ""

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

        return super(KotlinTranspiler, self).visit_Compare(node)

    def visit_Name(self, node):
        if node.id == "None":
            return "None"
        else:
            return super(KotlinTranspiler, self).visit_Name(node)

    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "None"
        else:
            return super(KotlinTranspiler, self).visit_NameConstant(node)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        # HACK to determine if main function name is visited
        if self.visit(node.test) == '__name__ == "__main__"':
            buf = ["fun main() {"]
            buf.extend([self.visit(child) for child in node.body])
            buf.append("")
            return "}\n".join(buf)
        return super().visit_If(node)

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super(KotlinTranspiler, self).visit_UnaryOp(node)

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
            return super(KotlinTranspiler, self).visit_BinOp(node)

    def visit_Module(self, node):
        buf = []
        for header in self._headers:
            buf.append(header)
        buf += [self.visit(b) for b in node.body]
        return "\n".join(buf)

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(KotlinTranspiler())
        extractor.visit(node)
        declarations = extractor.get_declarations()

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
            return "vec![{0}]".format(", ".join(elements))

        else:
            return "vec![]"

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
        return "assert!({0})".format(self.visit(node.test))

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
            mut = ""
            if is_mutable(node.scopes, get_id(target)):
                mut = "var "
            return "let {0}{1} = vec![{2}];".format(
                mut, self.visit(target), ", ".join(elements)
            )
        else:
            mut = ""
            if is_mutable(node.scopes, get_id(target)):
                mut = "var "

            target = self.visit(target)
            value = self.visit(node.value)

            if len(node.scopes) == 1:
                if isinstance(
                    node.scopes[0], ast.Module
                ):  # if assignment is module level it must be const
                    return "const {0}: _ = {1};".format(target, value)

            return "{0}{1} = {2}".format(mut, target, value)

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
        return "if {0} {{ {1} }} else {{ {2} }}".format(test, body, orelse)
