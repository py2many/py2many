import ast


class OperatorSymbols(ast.NodeVisitor):
    def visit_Eq(self, _):
        return '=='

    def visit_NotEq(self, _):
        return '!='

    def visit_Pass(self, _):
        return '/*pass*/'

    def visit_Mult(self, _):
        return '*'

    def visit_Add(self, _):
        return '+'

    def visit_Sub(self, _):
        return '-'

    def visit_Div(self, _):
        return '/'

    def visit_FloorDiv(self, _):
        return '/'

    def visit_Mod(self, _):
        return '%'

    def visit_Lt(self, _):
        return '<'

    def visit_Gt(self, _):
        return '>'

    def visit_GtE(self, _):
        return '>='

    def visit_LtE(self, _):
        return '<='

    def visit_LShift(self, _):
        return '<<'

    def visit_RShift(self, _):
        return '>>'

    def visit_BitXor(self, _):
        return '^'

    def visit_BitOr(self, _):
        return '|'

    def visit_BitAnd(self, _):
        return '&'

    def visit_Not(self, _):
        return '!'

    def visit_IsNot(self, _):
        return '!='

    def visit_USub(self, _):
        return '-'

    def visit_And(self, _):
        return '&&'

    def visit_Or(self, _):
        return '||'


class CLikeTranspiler(OperatorSymbols):
    """Provides a base for C-like programming languages"""
    def visit_Name(self, node):
        if node.id == 'True':
            return 'true'
        elif node.id == 'False':
            return 'false'
        return node.id

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
