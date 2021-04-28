import ast
import sys

from py2many.analysis import get_id
from typing import List, Tuple


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
    IGNORED_MODULE_LIST = set(
        ["typing", "enum", "dataclasses", "ctypes", "math", "__future__"]
    )

    def __init__(self):
        self._type_map = {}
        self._headers = set([])
        self._usings = set([])
        self._container_type_map = {}
        self._default_type = "auto"

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

    def _map_type(self, typename) -> str:
        return self._type_map.get(typename, self._default_type)

    def _map_types(self, typenames: List[str]) -> List[str]:
        return [self._map_type(e) for e in typenames]

    def _map_container_type(self, typename) -> str:
        return self._container_type_map.get(typename, self._default_type)

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}<{index_type}>"

    def _visit_container_type(self, typename: Tuple) -> str:
        value_type, index_type = typename
        value_type = self._map_container_type(value_type)
        if isinstance(index_type, List):
            index_contains_default = "Any" in index_type
            if not index_contains_default:
                index_type = [self._map_type(e) for e in index_type]
                index_type = ", ".join(index_type)
        else:
            index_contains_default = index_type == "Any"
            if not index_contains_default:
                index_type = self._map_type(index_type)
        # Avoid types like HashMap<_, foo>. Prefer default_type instead
        if index_contains_default:
            return self._default_type
        return self._combine_value_index(value_type, index_type)

    def _typename_from_annotation(self, node, attr="annotation") -> str:
        default_type = self._default_type
        typename = default_type
        if hasattr(node, attr):
            typename = getattr(node, attr)
            if isinstance(typename, ast.Subscript):
                # Store a tuple like (List, int) or (Dict, (str, int)) for container types
                # in node.container_type
                # And return a target specific type
                slice_value = self._slice_value(typename)
                if isinstance(slice_value, ast.Name):
                    slice_value = get_id(slice_value)
                elif isinstance(slice_value, ast.Tuple):
                    slice_value = [get_id(e) for e in slice_value.elts]
                node.container_type = (get_id(typename.value), slice_value)
                return self._visit_container_type(node.container_type)
            # TODO: get more disciplined about how we use type_map
            elif isinstance(typename, ast.Name):
                return self._map_type(get_id(typename))
            elif isinstance(typename, ast.ClassDef):
                return get_id(typename)
            else:
                raise Exception(typename, type(typename))
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
        return node.id

    def visit_NameConstant(self, node):
        if node.value is True:
            return "true"
        elif node.value is False:
            return "false"
        elif node.value is None:
            return "NULL"
        else:
            return node.value

    def visit_Constant(self, node):
        if isinstance(node.value, str):
            return self.visit_Str(node)
        return str(self.visit_NameConstant(node))

    def visit_Str(self, node):
        return f'"{node.value}"'

    def visit_arguments(self, node):
        args = [self.visit(arg) for arg in node.args]
        if args == []:
            return [], []
        typenames, args = map(list, zip(*args))
        return typenames, args

    def visit_Return(self, node):
        if node.value:
            return "return {0};".format(self.visit(node.value))
        return "return;"

    def _make_block(self, node):
        buf = []
        buf.append("({")
        buf.extend([self.visit(child) for child in node.body])
        buf.append("})")
        return "\n".join(buf)

    def visit_If(self, node, use_parens=True):
        buf = []
        # if True: s1; s2  should be transpiled into ({s1; s2;})
        # such that the value of the expression is s2
        # This is a idiom used by rewriters to transform a single ast Node s0
        # into multiple statements s1, s2
        make_block = (
            isinstance(node.test, ast.Constant)
            and node.test.value == True
            and node.orelse == []
        )
        if make_block:
            return self._make_block(node)
        else:
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
            return self.visit_In(node)

        left = self.visit(node.left)
        op = self.visit(node.ops[0])
        right = self.visit(node.comparators[0])

        return "{0} {1} {2}".format(left, op, right)

    def visit_BoolOp(self, node):
        op = self.visit(node.op)
        return op.join([self.visit(v) for v in node.values])

    def visit_UnaryOp(self, node):
        return "{0}({1})".format(self.visit(node.op), self.visit(node.operand))

    def visit_AugAssign(self, node):
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return "{0} {1}= {2};".format(target, op, val)

    def visit_AnnAssign(self, node):
        target = self.visit(node.target)
        if (
            isinstance(node.target.annotation, ast.Subscript)
            and get_id(node.target.annotation.value) == "Callable"
        ):
            type_str = self._default_type
        else:
            type_str = self._typename_from_annotation(node)
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
