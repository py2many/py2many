import sys
import ast
from .clike import CLikeTranspiler
from .scope import add_scope_context
from .context import add_variable_context, add_list_calls
from .analysis import add_imports, is_void_function, get_id
from .tracer import decltype, is_list, is_builtin_import, defined_before, is_class_or_module


def transpile(source, headers=False, testing=False):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    add_imports(tree)

    transpiler = RustTranspiler()

    buf = []
    if testing:
        buf += ['#include "catch.hpp"']
        transpiler.use_catch_test_cases = True

    if headers:
        buf += transpiler.headers
        buf += transpiler.usings

    if testing or headers:
        buf.append('')  # Force empty line

    cpp = transpiler.visit(tree)
    return "\n".join(buf) + cpp


def generate_catch_test_case(node, body):
    funcdef = 'TEST_CASE("{0}")'.format(node.name)
    return funcdef + " {\n" + body + "\n}"


def generate_template_fun(node, body):
    params = []
    arg_list = node.args.args
    has_self = arg_list and arg_list[0].arg == "self"
    if has_self:
        arg_list = arg_list[1:]

    for idx, arg in enumerate(arg_list):
        params.append(("T" + str(idx + 1), get_id(arg))) #TODO this get_id should be replaced by visit
    typenames = [arg[0] for arg in params]

    if is_void_function(node):
        return_type = ""
    else:
        return_type = "-> RT"
        typenames.append("RT")
    
    template = ""
    if len(typenames) > 0:
        template = "<{0}>".format(", ".join(typenames))
    params = ["{0}: {1}".format(arg[1], arg[0]) for arg in params]

    if has_self:
        params.insert(0, "&self")

    funcdef = "fn {0}{1}({2}) {3}".format(node.name, template,
                                          ", ".join(params), return_type)
    return funcdef + " {\n" + body + "\n}"


def generate_lambda_fun(node, body):
    params = ["auto {0}".format(param.id) for param in node.args.args]
    funcdef = "auto {0} = []({1})".format(node.name, ", ".join(params))
    return funcdef + " {\n" + body + "\n};"


class RustTranspiler(CLikeTranspiler):
    def __init__(self):
        self.headers = set(['use std::*;\n'])
        self.usings = set([])
        self.use_catch_test_cases = False

    def visit_FunctionDef(self, node):
        body = "\n".join([self.visit(n) for n in node.body])

        if (self.use_catch_test_cases and
            is_void_function(node) and
            node.name.startswith("test")):
            return generate_catch_test_case(node, body)
        # is_void_function(node) or is_recursive(node):
        return generate_template_fun(node, body)
        # else:
        #    return generate_lambda_fun(node, body)

    def visit_arg(self, node):
        return get_id(node)

    def visit_Lambda(self, node):
        args = [self.visit(n) for n in node.args.args]
        args_string = ", ".join(args)
        body = self.visit(node.body)
        return "|{0}| {{\n{1}}}".format(args_string, body)


    def visit_Attribute(self, node):
        attr = node.attr
        if node.lineno == 53:
            dnjfd = 4

        value_id = self.visit(node.value)
        if is_builtin_import(value_id):
            return "py14::" + value_id + "::" + attr
        elif value_id == "math":
            if node.attr == "asin":
                return "std::asin"
            elif node.attr == "atan":
                return "std::atan"
            elif node.attr == "acos":
                return "std::acos"

        if is_list(node.value):
            if node.attr == "append":
                attr = "push"
        if not value_id:
            value_id = ""

        if is_class_or_module(value_id, node.scopes):
            return "{0}::{1}".format(value_id, attr);

        return value_id + "." + attr

    def visit_Call(self, node):
        fname = self.visit(node.func)
        if node.args:
            args = [self.visit(a) for a in node.args]
            args = ", ".join(args)
        else:
            args = ''

        if fname == "int":
            return "py14::to_int({0})".format(args)
        elif fname == "str":
            return "std::to_string({0})".format(args)
        elif fname == "max":
            return "cmp::max({0})".format(args)
        elif fname == "min":
            return "cmp::min({0})".format(args)
        elif fname == "range" or fname == "xrange":
            if "," not in args: #one value range means 0..n
                return "0.." + args
            return args.replace(",","..")
        elif fname == "len":
            return "{0}.len()".format(self.visit(node.args[0]))
        elif fname == "print":
            buf = []
            for n in node.args:
                value = self.visit(n)
                buf.append('println!("{{:?}}",{0});'.format(value))
            return '\n'.join(buf)

        return '{0}({1})'.format(fname, args)

    def visit_For(self, node):
        target = self.visit(node.target)
        it = self.visit(node.iter)
        buf = []
        buf.append('for {0} in {1} {{'.format(target, it))
        buf.extend([self.visit(c) for c in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Expr(self, node):
        s = self.visit(node.value)
        if s.strip() and not s.endswith(';'):
            s += ';'
        if s == ';':
            return ''
        else:
            return s

    def visit_Str(self, node):
        return ("" +
                super(RustTranspiler, self).visit_Str(node) + "")

    def visit_Bytes(self, node):
        bytes_str = "{0}".format(node.s)
        return bytes_str.replace("'", '"') #replace single quote with double quote

    def visit_Compare(self, node):
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        if isinstance(node.ops[0], ast.In):
            return "{0}.iter().any(|&x| x == {1})".format(right, left) #is it too much?
        elif isinstance(node.ops[0], ast.NotIn):
            return "{0}.iter().all(|&x| x != {1})".format(right, left) #is it even more?
            
        return super(RustTranspiler, self).visit_Compare(node)

    def visit_Name(self, node):
        if node.id == 'None':
            return 'None'
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

        #HACK to determine if main function name is visited
        if self.visit(node.test) == '__name__ == "__main__"':
            buf = ["fn main() {",]
            buf.extend([self.visit(child) for child in node.body])
            buf.append("}")
            return "\n".join(buf)
        else:
            return ("".join(var_definitions) +
                    super(RustTranspiler, self).visit_If(node))

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
        if (isinstance(node.left, ast.List)
                and isinstance(node.op, ast.Mult)
                and isinstance(node.right, ast.Num)):
            return "std::vector ({0},{1})".format(self.visit(node.right),
                                                  self.visit(node.left.elts[0]))
        else:
            return super(RustTranspiler, self).visit_BinOp(node)

    def visit_Module(self, node):
        buf = [self.visit(b) for b in node.body]
        buf = [line for line in buf if line is not None]
        return "\n".join(buf)

    def visit_ClassDef(self, node):
        struct_def = "struct {0} {{\n}}\n\n".format(node.name);
        impl_def = "impl {0} {{\n".format(node.name);
        buf = [self.visit(b) for b in node.body]
        return "{0}{1}{2} \n}}".format(struct_def, impl_def, "\n".join(buf))

    def visit_alias(self, node):
        return 'use {0};'.format(node.name)

    def visit_Import(self, node):
        imports = [self.visit(n) for n in node.names]
        return "\n".join(i for i in imports if i)

    def visit_ImportFrom(self, node):
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

    def visit_Subscript(self, node):
        if isinstance(node.slice, ast.Ellipsis):
            raise NotImplementedError('Ellipsis not supported')

        index = ""

        if isinstance(node.slice, ast.Index):
            index = self.visit(node.slice.value)
        else:
            lower = ""
            if node.slice.lower:
                lower = self.visit(node.slice.lower)
            upper = ""
            if node.slice.upper:
                upper = self.visit(node.slice.upper)
                
            index = "{0}..{1}".format(lower, upper)

        value = self.visit(node.value)
        return "{0}[{1}]".format(value, index)

    def visit_Tuple(self, node):
        elts = [self.visit(e) for e in node.elts]
        return "({0})".format(", ".join(elts))

    def visit_unsupported_body(self, name, body):
        buf = ['let {0} = {{ //unsupported'.format(name)]
        buf += [self.visit(n) for n in body]
        buf.append('};')
        return buf;

    def visit_Try(self, node, finallybody=None):
        buf = self.visit_unsupported_body("try_dummy", node.body)

        for handler in node.handlers:
            buf += self.visit(handler)
        # buf.append("\n".join(excepts));

        if finallybody:
            buf += self.visit_unsupported_body("finally_dummy", finallybody)

        return '\n'.join(buf)

    def visit_ExceptHandler(self, node):
        name = "except!({0})".format(self.visit(node.type))
        body = self.visit_unsupported_body(name, node.body)
        return body

    def visit_Assert(self, node):
        return "assert!({0});".format(self.visit(node.test))

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

        if isinstance(target, ast.Subscript) or\
            isinstance(target, ast.Attribute):
            target = self.visit(target)
            value = self.visit(node.value)
            if value == None:
                value = 'None'
            return "{0} = {1};".format(target, value)

        # if isinstance(target, ast.Attribute):
        #     return "{0}.{1} = ;".format(target.value.id, target.attr)

        definition = node.scopes.find(target.id)
        if (isinstance(target, ast.Name) and
              defined_before(definition, node)):
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        elif isinstance(node.value, ast.List):
            elements = [self.visit(e) for e in node.value.elts]
            return "let mut {0} = vec![{1}];".format(self.visit(target), ", ".join(elements))
        else:
            target = self.visit(target)
            value = self.visit(node.value)
            return "let {0} = {1};".format(target, value)

    def visit_Delete(self, node):
        target = node.targets[0]
        return "{0}.drop();".format(self.visit(target))

    def visit_Raise(self, node):
        return "raise!({0}); //unsupported".format(self.visit(node.exc))

    def visit_With(self, node):
        return "with!({0}); //unsupported".format(self.visit(node.body))

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
        return '\n'.join(buf)

    def visit_ListComp(self, node):
        elt = self.visit(node.elt)
        generator = node.generators[0]
        target = self.visit(generator.target)
        iter = self.visit(generator.iter)        
        return "{0}.iter().map(|{1}| {2}).collect()".format(iter, target, elt)
