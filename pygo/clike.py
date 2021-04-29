import ast

from .inference import GO_TYPE_MAP

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


go_type_map = {
    "bool": "bool",
    "int": "int",
    "float": "float64",
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


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = GO_TYPE_MAP

    def visit_Name(self, node):
        if node.id in go_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            self._usings.add('"math"')
            return "math.Pow({0}, {1})".format(
                self.visit(node.left), self.visit(node.right)
            )

        # Multiplication and division binds tighter (has higher precedence) than addition and subtraction.
        # To visually communicate this we omit spaces when multiplying and dividing.
        if isinstance(node.op, (ast.Mult, ast.Div)):
            return "({0}{1}{2})".format(
                self.visit(node.left), self.visit(node.op), self.visit(node.right)
            )

        else:
            return "({0} {1} {2})".format(
                self.visit(node.left), self.visit(node.op), self.visit(node.right)
            )

    def visit_In(self, node):
        self._usings.add('"github.com/adsharma/py2many/pygo"')
        container = self.visit(node.left)
        element = self.visit(node.comparators[0])
        return f"pygo.contains({container}, {element})"
