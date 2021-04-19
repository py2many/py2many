import ast
import sys

from py2many.analysis import get_id


symbols = {
    ast.Eq: "==",
    ast.Is: "==",
    ast.NotEq: "!=",
    ast.Mult: "*",
    ast.Add: "+",
    ast.Sub: "-",
    ast.Div: "/",
    ast.FloorDiv: "/",
    ast.Mod: "%",
    ast.Lt: "<",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.LtE: "<=",
    ast.LShift: "<<",
    ast.RShift: ">>",
    ast.BitXor: "^",
    ast.BitOr: "|",
    ast.BitAnd: "&",
    ast.Not: "!",
    ast.IsNot: "!=",
    ast.USub: "-",
    ast.And: "&&",
    ast.Or: "||",
    ast.In: "in",
}


def c_symbol(node):
    """Find the equivalent C symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return symbols[symbol_type]


class CLikeTranspiler(ast.NodeVisitor):
    """Provides a base for C-like programming languages"""

    builtin_constants = frozenset(["True", "False"])
    IGNORED_MODULE_LIST = set(["typing", "enum", "dataclasses", "ctypes", "__future__"])

    def __init__(self):
        self._type_map = {}
        self._headers = set([])
        self._usings = set([])

    def headers(self, meta=None):
        return ""

    def usings(self):
        return ""

    def comment(self, text):
        return f"/* {text} */"

    def _cast(self, name: str, to) -> str:
        return f"({to}) {name}"

    def _slice_value(self, node: ast.AST):
        # 3.9 compatibility shim
        if sys.version_info < (3, 9, 0):
            if not isinstance(node.slice, ast.Index):
                raise NotImplementedError("Advanced Slicing not supported")
            slice_value = node.slice.value
        else:
            slice_value = node.slice
        return slice_value

    def _typename_from_annotation(self, node, default_type) -> str:
        typename = default_type
        if hasattr(node, "annotation"):
            typename = get_id(node.annotation)
            # TODO: get more disciplined about how we use type_map
            if not isinstance(typename, str):
                typename = self.visit(typename)
                typename = self._type_map.get(typename, default_type)
            else:
                if typename in self._type_map:
                    typename = self._type_map[typename]
        return typename

    def visit(self, node):
        if type(node) == ast.Pass:
            return self.comment("pass")
        if type(node) in symbols:
            return c_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node):
        if node.id in self.builtin_constants:
            return node.id.lower()
        elif hasattr(node, "is_annotation"):
            if node.id in self._type_map:
                return self._type_map[node.id]
        elif hasattr(node, "annotation") and hasattr(node.annotation, "id"):
            if node.annotation.id in self._type_map:
                node.annotation.id = self._type_map[node.annotation.id]
        return node.id

    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        else:
            return node.value

    def visit_Constant(self, node):
        if isinstance(node.value, str):
            return self.visit_Str(node)
        return str(node.n)

    def visit_Str(self, node):
        return f'"{node.value}"'

    def visit_Return(self, node):
        if node.value:
            return "return {0};".format(self.visit(node.value))
        return "return;"

    def visit_If(self, node, use_parens=True):
        buf = []
        if use_parens:
            buf.append("if({0}) {{".format(self.visit(node.test)))
        else:
            buf.append("if {0} {{".format(self.visit(node.test)))
        buf.extend([self.visit(child) for child in node.body])

        orelse = [self.visit(child) for child in node.orelse]
        if orelse:
            buf.append("} else {")
            buf.extend(orelse)
            buf.append("}")
        else:
            buf.append("}")

        return "\n".join(buf)

    def visit_Continue(self, node):
        return "continue;"

    def visit_Break(self, node):
        return "break;"

    def visit_While(self, node, use_parens=True):
        buf = []
        if use_parens:
            buf.append("while ({0}) {{".format(self.visit(node.test)))
        else:
            buf.append("while {0} {{".format(self.visit(node.test)))
        buf.extend([self.visit(n) for n in node.body])
        buf.append("}")
        return "\n".join(buf)

    def visit_Compare(self, node):
        if isinstance(node.ops[0], ast.In):
            return self.visit_Any(node)

        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node.comparators[0])

        return "{0} {1} {2}".format(left, op, right)

    def visit_BoolOp(self, node):
        op = self.visit(node.op)
        return op.join([self.visit(v) for v in node.values])

    def visit_UnaryOp(self, node):
        return "{0}{1}".format(self.visit(node.op), self.visit(node.operand))

    def visit_AugAssign(self, node):
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2};".format(target, op, val)

    def visit_AnnAssign(self, node):
        target = self.visit(node.target)
        type_str = self.visit(node.annotation)
        val = self.visit(node.value) if node.value is not None else None
        return (target, type_str, val)

    def visit_ClassDef(self, node):
        bases = [get_id(base) for base in node.bases]
        if set(bases) == {"Enum", "str"}:
            return self.visit_StrEnum(node)
        if len(bases) != 1:
            return None
        if not bases[0] in {"IntEnum", "IntFlag"}:
            return None
        if bases == ["IntEnum"]:
            return self.visit_IntEnum(node)
        if bases == ["IntFlag"]:
            return self.visit_IntFlag(node)

    def visit_StrEnum(self, node):
        raise Exception("Unimplemented")

    def visit_IntEnum(self, node):
        raise Exception("Unimplemented")

    def visit_IntFlag(self, node):
        raise Exception("Unimplemented")
