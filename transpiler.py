import ast


def transpile(source):
    tree = ast.parse(source)
    cpp = CppTranspiler().visit(tree)
    return cpp


class CLikeTranspiler(ast.NodeVisitor):
    """Provides a base for C-like programming languages"""

    def visit_Name(self, node):
        if node.id == 'True':
            return 'true'
        elif node.id == 'False':
            return 'false'
        return node.id

    def visit_Eq(self, node):
        return '=='

    def visit_NotEq(self, node):
        return '!='

    def visit_Num(self, node):
        return str(node.n)

    def visit_Pass(self, node):
        return '/*pass*/'

    def visit_Mult(self, node):
        return '*'

    def visit_Add(self, node):
        return '+'

    def visit_Sub(self, node):
        return '-'

    def visit_Div(self, node):
        return '/'

    def visit_Mod(self, node):
        return '%'

    def visit_Lt(self, node):
        return '<'

    def visit_Gt(self, node):
        return '>'

    def visit_GtE(self, node):
        return '>='

    def visit_LtE(self, node):
        return '<='

    def visit_LShift(self, node):
        return '<<'

    def visit_RShift(self, node):
        return '>>'

    def visit_BitXor(self, node):
        return '^'

    def visit_BitOr(self, node):
        return '|'

    def visit_BitAnd(self, node):
        return '&'

    def visit_Not(self, node):
        return '!'

    def visit_IsNot(self, node):
        return '!=='

    def visit_USub(self, node):
        return '-'

    def visit_And(self, node):
        return ' && '

    def visit_Or(self, node):
        return ' || '

    def visit_Str(self, node):
        return '"{0}"'.format(node.s)

    def visit_Return(self, node):
        if node.value:
            return 'return {0};'.format(self.visit(node.value))
        return 'return;'

    def visit_If(self, node):
        buffer = []
        buffer.append('if ({0}) {{'.format(self.visit(node.test)))
        buffer.extend([self.visit(child) for child in node.body])

        orelse = [self.visit(child) for child in node.orelse]
        if orelse:
            buffer.append('} else {')
            buffer.extend(orelse)
            buffer.append("}")

        return '\n'.join(buffer)

    def visit_Print(self, node):
        buffer = ["std::cout"]
        for n in node.values:
            value = self.visit(n)
            buffer.append("<<")
            buffer.append(value)
        return " ".join(buffer) + "<< std::endl;"

    def visit_While(self, node):
        buffer = []
        buffer.append("while ({0}) {{".format(self.visit(node.test)))
        buffer.extend([self.visit(c) for c in node.body])
        buffer.append("}")
        return '\n'.join(buffer)

    def visit_Compare(self, node):
        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node.comparators[0])
        return "{0} {1} {2}".format(left, op, right)

    def visit_BinOp(self, node):
        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)
        return " ".join([left, op, right])

    def visit_AugAssign(self, node):
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2};".format(target, op, val)


class CppTranspiler(CLikeTranspiler):
    def __init__(self):
        self._function_stack = []
        self._vars = set()

    def visit_FunctionDef(self, node):
        self._function_stack.append(node)

        args = []
        for idx, arg in enumerate(node.args.args):
            args.append(("T" + str(idx + 1), arg.id))

        typenames = ["typename " + arg[0] for arg in args]
        template = "template <{0}>".format(",".join(typenames))
        params = ["{0} {1}".format(arg[0], arg[1]) for arg in args]
        funcdef = "{0}\nauto {1} ({2})".format(template,
                                               node.name,
                                               ",".join(params))

        body = [self.visit(child) for child in node.body]
        self._function_stack.pop()
        return funcdef + " {\n" + "\n".join(body) + "\n}"

    def visit_Call(self, node):
        fname = self.visit(node.func)
        if node.args:
            args = [self.visit(a) for a in node.args]
            args = ", ".join(args)
        else:
            args = ''
        return '{0}({1})'.format(fname, args)

    def visit_For(self, node):
        target = self.visit(node.target)
        iter = self.visit(node.iter)
        buffer = []
        buffer.append('for(auto {0}:{1} {{'.format(target, iter))
        buffer.extend([self.visit(c) for c in node.body])
        buffer.append("}")
        return "\n".join(buffer)

    def visit_Expr(self, node):
        s = self.visit(node.value)
        if s.strip() and not s.endswith(';'):
            s += ';'
        if s == ';':
            return ''
        else:
            return s

    def visit_Str(self, node):
        """Use a C++ 14 string literal instead of raw string"""
        return super(CppTranspiler, self).visit_Str(node) + "s"

    def visit_Name(self, node):
        if node.id == 'None':
            return 'nullptr'
        else:
            return super(CppTranspiler, self).visit_Name(node)

    def visit_If(self, node):
        if self.visit(node.test) == '__name__ == "__main__"s':
            buffer = ["int main(int argc, char * argv[]) {",
                      "python::init(argc, argv);"]
            buffer.extend([self.visit(child) for child in node.body])
            buffer.append("}")
            return "\n".join(buffer)

        else:
            return super(CppTranspiler, self).visit_If(node)

    def visit_BinOp(self, node):
        if (isinstance(node.left, ast.List)
                and isinstance(node.op, ast.Mult)
                and isinstance(node.right, ast.Num)):
            return "std::vector ({0},{1})".format(self.visit(node.right),
                                                  self.visit(node.left.elts[0]))
        else:
            return super(CppTranspiler, self).visit_BinOp(node)

    def visit_Module(self, node):
        lines = []
        for b in node.body:
            line = self.visit(b)
            lines.append(line)

        return "\n".join(filter(None, lines))

    def visit_alias(self, node):
        if node.name == "sys":
            return '#include "sys.h"'

    def visit_Import(self, node):
        print(node)
        imports = [self.visit(n) for n in node.names]
        return "\n".join(filter(None, imports))

    def visit_List(self, node):
        elements = [self.visit(e) for e in node.elts]
        return "[" + ",".join(elements) + "]"

    def visit_Subscript(self, node):
        value = self.visit(node.value)

        if not isinstance(node.slice, ast.Index):
            print("Not supported")

        if isinstance(node.ctx, ast.Load):
            return "{0}[{1}]".format(value, node.slice.value)

    def visit_Assign(self, node):
        target = node.targets[0]

        if isinstance(target, ast.Name) and target.id in self._vars:
            target = self.visit(target)
            value = self.visit(node.value)
            return "{0} = {1};".format(target, value)
        else:
            target = self.visit(target)
            value = self.visit(node.value)
            self._vars.add(target)
            return "auto {0} = {1};".format(target, value)
