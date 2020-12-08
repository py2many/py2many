import ast


symbols = {
    ast.Eq: "==",
    ast.NotEq: '!=',
    ast.Pass: '/*pass*/',
    ast.Mult: '*',
    ast.Add: '+',
    ast.Sub: '-',
    ast.Div: '/',
    ast.FloorDiv: '/',
    ast.Mod: '%',
    ast.Lt: '<',
    ast.Gt: '>',
    ast.GtE: '>=',
    ast.LtE: '<=',
    ast.LShift: '<<',
    ast.RShift: '>>',
    ast.BitXor: '^',
    ast.BitOr: '|',
    ast.BitAnd: '&',
    ast.Not: '!',
    ast.IsNot: '!=',
    ast.USub: '-',
    ast.And: '&&',
    ast.Or: '||'
}


def c_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return symbols[symbol_type]


class CLikeTranspiler(ast.NodeVisitor):
    builtin_constants = frozenset(['True', 'False', 'None'])
    """Provides a base for C-like programming languages"""
    def visit(self, node):
        if type(node) in symbols:
            return c_symbol(node)
        else:
            return super(CLikeTranspiler, self).visit(node)

    def visit_Name(self, node):
        if node.id in self.builtin_constants:
            return node.id.lower()
        return node.id
    
    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        else:
            return node.value

    def visit_Num(self, node):
        return str(node.n)

    def visit_Str(self, node):
        return '"{0}"'.format(node.s)

    def visit_Return(self, node):
        if node.value:
            return 'return {0};'.format(self.visit(node.value))
        return 'return;'

    def visit_If(self, node):
        buf = []
        buf.append('if({0}) {{'.format(self.visit(node.test)))
        buf.extend([self.visit(child) for child in node.body])

        orelse = [self.visit(child) for child in node.orelse]
        if orelse:
            buf.append('} else {')
            buf.extend(orelse)
            buf.append("}")
        else:
            buf.append('}')

        return '\n'.join(buf)

    def visit_While(self, node):
        buf = []
        buf.append("while ({0}) {{".format(self.visit(node.test)))
        buf.extend([self.visit(n) for n in node.body])
        buf.append("}")
        return '\n'.join(buf)

    def visit_Compare(self, node):
        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node.comparators[0])
        return "{0} {1} {2}".format(left, op, right)

    def visit_BoolOp(self, node):
        op = self.visit(node.op)
        return op.join([self.visit(v) for v in node.values])

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            return "std::pow({0}, {1})".format(self.visit(node.left),
                                               self.visit(node.right))

        return " ".join([self.visit(node.left),
                         self.visit(node.op),
                         self.visit(node.right)])

    def visit_AugAssign(self, node):
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2};".format(target, op, val)
