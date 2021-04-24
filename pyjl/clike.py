import ast

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


julia_type_map = {
    "bool": "Bool",
    "int": "Int64",
    "float": "Float64",
    "bytes": "Array{UInt8}",
    "str": "String",
    "c_int8": "Int8",
    "c_int16": "Int16",
    "c_int32": "Int32",
    "c_int64": "Int64",
    "c_uint8": "UInt8",
    "c_uint16": "UInt16",
    "c_uint32": "UInt32",
    "c_uint64": "UInt64",
}

# allowed as names in Python but treated as keywords in Julia
julia_keywords = frozenset(
    [
        "abstract",
        "baremodule",
        "begin",
        "break",
        "catch",
        "const",
        "continue",
        "do",
        "else",
        "elseif",
        "end",
        "export",
        "false",
        "finally",
        "for",
        "function",
        "global",
        "if",
        "import",
        "let",
        "local",
        "macro",
        "module",
        "mutable",
        "primitive",
        "quote",
        "return",
        "struct",
        "true",
        "try",
        "type",
        "using",
        "while",
    ]
)


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = julia_type_map

    def visit_Name(self, node):
        if node.id in julia_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            return "pow({0}, {1})".format(self.visit(node.left), self.visit(node.right))

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
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"
