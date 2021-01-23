import sys
import ast

from .clike import CLikeTranspiler
from .declaration_extractor import DeclarationExtractor
from common.tracer import (
    decltype,
    is_list,
    is_builtin_import,
    defined_before,
    is_class_or_module,
)

from common.scope import add_scope_context
from common.annotation_transformer import add_annotation_flags
from common.mutability_transformer import detect_mutable_vars
from common.context import add_variable_context, add_list_calls
from common.analysis import add_imports, is_void_function, get_id, is_mutable

container_types = {"List": "Vec", "Dict": "HashMap", "Set": "Set", "Optional": "Option"}


def transpile(source):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    add_annotation_flags(tree)
    add_imports(tree)

    transpiler = RustTranspiler()

    return transpiler.visit(tree)


class RustTranspiler(CLikeTranspiler):
    def __init__(self):
        self.headers = ["use std::*;", "use std::collections::HashMap;", ""]

    def visit_FunctionDef(self, node):
        body = "\n".join([self.visit(n) for n in node.body])
        typenames, args = self.visit(node.args)

        args_list = []
        if args and args[0] == "self":
            del typenames[0]
            del args[0]
            args_list.append("&self")

        typedecls = []
        index = 0
        for i in range(len(args)):
            typename = typenames[i]
            arg = args[i]
            if typename == "T":
                typename = "T{0}".format(index)
                typedecls.append(typename)
                index += 1
            args_list.append("{0}: {1}".format(arg, typename))

        return_type = ""
        if not is_void_function(node):
            if node.returns:
                return_type = "-> {0}".format(self.visit(node.returns))
            else:
                return_type = "-> RT"
                typedecls.append("RT")

        template = ""
        if len(typedecls) > 0:
            template = "<{0}>".format(", ".join(typedecls))

        funcdef = "fn {0}{1}({2}) {3}".format(
            node.name, template, ", ".join(args_list), return_type
        )
        return funcdef + " {\n" + body + "\n}"

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

    def visit_Call(self, node):
        fname = self.visit(node.func)

        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]
        if node.keywords:
            args += [self.visit(kw.value) for kw in node.keywords]

        if args:
            args = ", ".join(args)
        else:
            args = ""

        if fname == "int":
            return "i32::from({0})".format(args)
        elif fname == "str":
            return "String::from({0})".format(args)

        elif fname == "range" or fname == "xrange":

            vargs = list(map(self.visit, node.args))

            if len(node.args) == 1:
                return "(0..{})".format(vargs[0])
            elif len(node.args) == 2:
                return "({}..{})".format(vargs[0], vargs[1])
            elif len(node.args) == 3:
                return "({}..{}).step_by({})".format(vargs[0], vargs[1], vargs[2])
            else:
                raise Exception(
                    "encountered range() call with unknown parameters: range({})".format(
                        args
                    )
                )

        elif fname == "len":
            return "{0}.len()".format(self.visit(node.args[0]))
        elif fname == "enumerate":
            return "{0}.iter().enumerate()".format(self.visit(node.args[0]))
        elif fname == "sum":
            return "{0}.iter().sum()".format(self.visit(node.args[0]))
        elif fname == "max":
            return "{0}.iter().max().unwrap()".format(self.visit(node.args[0]))
        elif fname == "min":
            return "{0}.iter().min().unwrap()".format(self.visit(node.args[0]))
        elif fname == "reversed":
            return "{0}.iter().rev()".format(self.visit(node.args[0]))
        elif fname == "map":
            return "{0}.iter().map({1})".format(
                self.visit(node.args[1]), self.visit(node.args[0])
            )
        elif fname == "filter":
            return "{0}.into_iter().filter({1})".format(
                self.visit(node.args[1]), self.visit(node.args[0])
            )
        elif fname == "list":
            return "{0}.collect::<Vec<_>>()".format(self.visit(node.args[0]))
        elif fname == "print":
            values = []
            placeholders = []
            for n in node.args:
                values.append(self.visit(n))
                placeholders.append("{:?} ")
            return 'println!("{0}",{1});'.format(
                "".join(placeholders), ", ".join(values)
            )

        return "{0}({1})".format(fname, args)

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append("for {0} in {1} {{".format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Expr(self, node):
        s = self.visit(node.value)
        if s.strip() and not s.endswith(";"):
            s += ";"
        if s == ";":
            return ""
        else:
            return s

    def visit_Str(self, node):
        return "" + super(RustTranspiler, self).visit_Str(node) + ""

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

        return super(RustTranspiler, self).visit_Compare(node)

    def visit_Name(self, node):
        if node.id == "None":
            return "None"
        else:
            return super(RustTranspiler, self).visit_Name(node)

    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "None"
        else:
            return super(RustTranspiler, self).visit_NameConstant(node)

    def visit_If(self, node):
        body_vars = set([get_id(v) for v in node.scopes[-1].body_vars])
        orelse_vars = set([get_id(v) for v in node.scopes[-1].orelse_vars])
        node.common_vars = body_vars.intersection(orelse_vars)

        # TODO find out if this can be useful
        var_definitions = []
        # for cv in node.common_vars:
        #     definition = node.scopes.find(cv)
        #     var_type = decltype(definition)
        #     var_definitions.append("{0} {1};\n".format(var_type, cv))

        # HACK to determine if main function name is visited
        if self.visit(node.test) == '__name__ == "__main__"':
            buf = ["fn main() {"]
            buf.extend([self.visit(child) for child in node.body])
            buf.append("}")
            return "\n".join(buf)
        else:
            return "".join(var_definitions) + super(RustTranspiler, self).visit_If(
                node, use_parens=False
            )

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return "-{0}".format(self.visit(node.operand))
            else:
                return "-({0})".format(self.visit(node.operand))
        else:
            return super(RustTranspiler, self).visit_UnaryOp(node)

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
            return super(RustTranspiler, self).visit_BinOp(node)

    def visit_Module(self, node):
        buf = []
        for header in self.headers:
            buf.append(header)
        buf += [self.visit(b) for b in node.body]
        return "\n".join(buf)

    def visit_ClassDef(self, node):
        extractor = DeclarationExtractor(RustTranspiler())
        extractor.visit(node)
        declarations = extractor.get_declarations()

        fields = []
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = "ST{0}".format(index)
                index += 1
            fields.append("{0}: {1},".format(declaration, typename))

        struct_def = "struct {0} {{\n{1}\n}}\n\n".format(node.name, "\n".join(fields))
        impl_def = "impl {0} {{\n".format(node.name)
        buf = [self.visit(b) for b in node.body]
        return "{0}{1}{2} \n}}".format(struct_def, impl_def, "\n".join(buf))

    def visit_alias(self, node):
        return "use {0};".format(node.name)

    def visit_Import(self, node):
        imports = [self.visit(n) for n in node.names]
        return "\n".join(i for i in imports if i)

    def visit_ImportFrom(self, node):
        if node.module == "typing" or node.module == "enum":
            return ""

        names = [n.name for n in node.names]
        names = ", ".join(names)
        module_path = node.module.replace(".", "::")
        return "use {0}::{{{1}}};".format(module_path, names)

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
        return "assert!({0});".format(self.visit(node.test))

    def visit_AnnAssign(self, node):
        target = self.visit(node.target)
        type_str = self.visit(node.annotation)
        val = self.visit(node.value)
        return "let {0}: {1} = {2};".format(target, type_str, val)

    def visit_Assign(self, node):
        target = node.targets[0]

        if isinstance(target, ast.Tuple):
            elts = [self.visit(e) for e in target.elts]
            value = self.visit(node.value)
            return "let ({0}) = {1};".format(", ".join(elts), value)

        if isinstance(node.scopes[-1], ast.If):
            outer_if = node.scopes[-1]
            target_id = self.visit(target)
            if target_id in outer_if.common_vars:
                value = self.visit(node.value)
                return "{0} = {1};".format(target_id, value)

        if isinstance(target, ast.Subscript) or isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            if value == None:
                value = "None"
            return "{0} = {1};".format(target, value)

        definition = node.scopes.find(target.id)
        if isinstance(target, ast.Name) and defined_before(definition, node):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            mut = ""
            if is_mutable(node.scopes, get_id(target)):
                mut = "mut "
            return "let {0}{1} = vec![{2}];".format(
                mut, self.visit(target), ", ".join(elements)
            )
        else:
            mut = ""
            if is_mutable(node.scopes, get_id(target)):
                mut = "mut "

            target = self.visit(target)
            value = self.visit(node.value)

            if len(node.scopes) == 1:
                if isinstance(
                    node.scopes[0], ast.Module
                ):  # if assignment is module level it must be const
                    return "const {0}: _ = {1};".format(target, value)

            return "let {0}{1} = {2};".format(mut, target, value)

    def visit_Delete(self, node):
        target = node.targets[0]
        return "{0}.drop();".format(self.visit(target))

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
            buf.append('println!("{{:?}}",{0});'.format(value))
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
