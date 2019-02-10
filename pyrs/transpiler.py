import sys
import ast
from .clike import CLikeTranspiler
from .scope import add_scope_context
from .context import add_variable_context, add_list_calls
from .analysis import add_imports, is_void_function, get_id
from .tracer import decltype, is_list, is_builtin_import, defined_before, is_class_or_module


def transpile(source):
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

    return transpiler.visit(tree)


class RustTranspiler(CLikeTranspiler):
    def __init__(self):
        self.headers = set(['use std::*;\n'])
        self.usings = set([])
        self.use_catch_test_cases = False

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

        funcdef = "fn {0}{1}({2}) {3}".format(node.name, template,
                                          ", ".join(args_list), return_type)
        return funcdef + " {\n" + body + "\n}"

    def visit_arguments(self, node):
        args = [self.visit(arg) for arg in node.args]

        #switch to zip
        types = []
        names = []
        for arg in args:
            types.append(arg[0])
            names.append(arg[1])

        return types,names

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
        return "|{0}| {{\n{1}}}".format(args_string, body)


    def visit_Attribute(self, node):
        attr = node.attr

        value_id = self.visit(node.value)
        if is_builtin_import(value_id):
            return "pyrs::" + value_id + "::" + attr
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

        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]
        if node.keywords:
            args += [self.visit(kw.value) for kw in node.keywords]
        
        if args:
            args = ", ".join(args)
        else:
            args = ''

        if fname == "int":
            return "pyrs::to_int({0})".format(args)
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
        elif fname == "enumerate":
            return "{0}.iter().enumerate()".format(self.visit(node.args[0]))
        elif fname == "sum":
            return "{0}.iter().sum()".format(self.visit(node.args[0]))
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
        return "\n".join(buf)

    def visit_init_function(self, node):
        members = []
        for child in node.body:
            if isinstance(child, ast.Assign):
                for target in child.targets:
                    if hasattr(target, "value"):
                        if self.visit(target.value) == "self":
                            members.append(target.attr)
        fields = []
        for idx, name in enumerate(members):
            fields.append("{0}: ST{1},".format(name, idx))
        return "\n".join(fields)

    def visit_ClassDef(self, node):
        class_members = ""
        for func in node.body:
            if isinstance(func, ast.FunctionDef):
                if func.name == "__init__":
                    class_members = self.visit_init_function(func)

        struct_def = "struct {0} {{\n{1}\n}}\n\n".format(node.name, class_members);
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
        if isinstance(node.slice, ast.Ellipsis):
            return "compile_error!('Elipsis is not supported');"

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
            
            if len(node.scopes) == 1:
                if isinstance(node.scopes[0], ast.Module): #if assignment is module level it must be const
                    return "const {0}: _ = {1};".format(target, value)

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

    def visit_DictComp(self, node):
        return "DictComp /*unimplemented()*/"

    def visit_GeneratorExp(self, node):
        elt = self.visit(node.elt)
        generator = node.generators[0]
        target = self.visit(generator.target)
        iter = self.visit(generator.iter)        
        return "{0}.iter().map(|{1}| {2}).collect::<Vec<_>>()".format(iter, target, elt)

    def visit_ListComp(self, node):
        return self.visit_GeneratorExp(node) #right now they are the same
