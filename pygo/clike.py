import ast

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

from .inference import GO_CONTAINER_TYPE_MAP, GO_TYPE_MAP, GO_WIDTH_RANK

go_type_map = {
    "bool": "bool",
    "int": "int",
    "float": "float64",
    "complex": "complex128",
    "bytes": "[]uint8",
    "str": "string",
    "c_int8": "int8",
    "c_int16": "int16",
    "c_int32": "int32",
    "c_int64": "int64",
    "c_uint8": "uint8",
    "c_uint16": "uint16",
    "c_uint32": "uint32",
    "c_uint64": "uint64",
}

# allowed as names in Python but treated as keywords in Go
go_keywords = frozenset(
    [
        "break",
        "default",
        "func",
        "interface",
        "select",
        "case",
        "defer",
        "go",
        "map",
        "struct",
        "chan",
        "else",
        "goto",
        "package",
        "switch",
        "const",
        "fallthrough",
        "if",
        "range",
        "type",
        "continue",
        "for",
        "import",
        "return",
        "var",
    ]
)

go_symbols = {ast.BitAnd: "&&", ast.BitOr: "||", ast.BitXor: "!="}


def go_symbol(node):
    """Find the equivalent Go symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return go_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        CommonCLikeTranspiler._type_map = GO_TYPE_MAP
        CLikeTranspiler._container_type_map = GO_CONTAINER_TYPE_MAP

    def visit(self, node) -> str:
        if type(node) in go_symbols:
            return go_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node) -> str:
        if node.id in go_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Pow):
            self._usings.add('"math"')
            left = self.visit(node.left)
            right = self.visit(node.right)
            pow_call = f"math.Pow(float64({left}), float64({right}))"
            if (
                isinstance(node.left, ast.Constant)
                and isinstance(node.left.value, int)
                and isinstance(node.right, ast.Constant)
                and isinstance(node.right.value, int)
            ):
                return f"int({pow_call})"
            return pow_call

        if isinstance(node.op, ast.Mult):
            if isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
                self._usings.add('"strings"')
                return (
                    f"strings.Repeat({self.visit(node.left)}, {self.visit(node.right)})"
                )
            if isinstance(node.right, ast.Constant) and isinstance(
                node.right.value, str
            ):
                self._usings.add('"strings"')
                return (
                    f"strings.Repeat({self.visit(node.right)}, {self.visit(node.left)})"
                )
            if isinstance(node.left, ast.List):
                return self._visit_slice_repeat(node.left, node.right)
            if isinstance(node.right, ast.List):
                return self._visit_slice_repeat(node.right, node.left)

        left = self.visit(node.left)
        op = self.visit(node.op)
        right = self.visit(node.right)

        left_type = self._typename_from_annotation(node.left)
        right_type = self._typename_from_annotation(node.right)

        left_rank = GO_WIDTH_RANK.get(left_type, -1)
        right_rank = GO_WIDTH_RANK.get(right_type, -1)

        if left_rank > right_rank:
            right = f"{left_type}({right})"
        elif right_rank > left_rank:
            left = f"{right_type}({left})"

        # Multiplication and division binds tighter (has higher precedence) than addition and subtraction.
        # To visually communicate this we omit spaces when multiplying and dividing.
        if isinstance(node.op, (ast.Mult, ast.Div)):
            return f"({left}{op}{right})"
        else:
            return f"({left} {op} {right})"

    def _visit_slice_repeat(self, list_node, count_node) -> str:
        element_type = self._default_type
        if hasattr(list_node, "container_type"):
            _, element_type = list_node.container_type
        if element_type is None and list_node.elts:
            from .inference import get_inferred_go_type

            element_type = get_inferred_go_type(list_node.elts[0])
        elements = ", ".join(self.visit(e) for e in list_node.elts)
        list_expr = f"[]{element_type}{{{elements}}}"
        count = self.visit(count_node)
        return (
            f"func() []{element_type} {{ "
            f"var out []{element_type}; "
            f"for i := 0; i < {count}; i++ {{ out = append(out, {list_expr}...) }}; "
            f"return out "
            f"}}()"
        )

    def visit_In(self, node) -> str:
        self._usings.add('"github.com/electrious/refutil"')
        element = self.visit(node.left)
        container = node.comparators[0]
        self._generic_typename_from_annotation(container)
        container_str = self.visit(container)
        if hasattr(container, "generic_container_type"):
            container_type, _ = container.generic_container_type
            if container_type in {"Set" or "Dict"}:
                return f"refutil.ContainsKey({container_str}, {element})"
        return f"refutil.Contains({container_str}, {element})"

    def _recursive_expand(self, slice_value):
        if isinstance(slice_value, ast.Name):
            slice_value = get_id(slice_value)
        elif isinstance(slice_value, (ast.Tuple, ast.List)):
            slice_value = [self._recursive_expand(e) for e in slice_value.elts]
        return slice_value

    def _typename_from_annotation(self, node, attr="annotation") -> str:
        if hasattr(node, attr):
            typename = getattr(node, attr)
            if isinstance(typename, ast.Subscript):
                if get_id(typename.value) == "Callable":
                    slice_value = self._slice_value(typename)
                    slice_value = self._recursive_expand(slice_value)

                    def recursive_tuple(lst) -> tuple:
                        return (
                            tuple(recursive_tuple(x) for x in lst)
                            if isinstance(lst, list)
                            else lst
                        )

                    slice_value = recursive_tuple(slice_value)
                    if len(slice_value) == 2:
                        # Kotlin lambda syntax
                        args = ", ".join(self._map_types(slice_value[0]))
                        ret = self._map_type(slice_value[1])
                        return f"func({args}) {ret}"
                    return f"{slice_value}"

        return super()._typename_from_annotation(node, attr)
