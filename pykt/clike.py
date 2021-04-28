import ast

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler


kotlin_type_map = {
    "bool": "Boolean",
    "int": "Int",
    "float": "Double",
    "bytes": "ByteArray",
    "str": "String",
    "c_int8": "Byte",
    "c_int16": "Short",
    "c_int32": "Int",
    "c_int64": "Long",
    "c_uint8": "UByte",
    "c_uint16": "UShort",
    "c_uint32": "UInt",
    "c_uint64": "ULong",
}

# allowed as names in Python but treated as keywords in Kotlin
kotlin_keywords = frozenset(
    [
        "abstract",
        "actual",
        "annotation",
        "as",
        "break",
        "by",
        "catch",
        "class",
        "companion",
        "const",
        "constructor",
        "continue",
        "crossinline",
        "data",
        "delegate",
        "do",
        "dynamic",
        "else",
        "enum",
        "expect",
        "external",
        "field",
        "file",
        "file",
        "final",
        "finally",
        "for",
        "fun",
        "get",
        "if",
        "import",
        "in",
        "infix",
        "init",
        "inline",
        "inner",
        "interface",
        "internal",
        "is",
        "lateinit",
        "noinline",
        "object",
        "open",
        "operator",
        "out",
        "override",
        "package",
        "param",
        "private",
        "property",
        "protected",
        "public",
        "receiver",
        "reified",
        "return",
        "sealed",
        "set",
        "setparam",
        "super",
        "suspend",
        "tailrec",
        "this",
        "throw",
        "try",
        "typealias",
        "typeof",
        "val",
        "var",
        "vararg",
        "when",
        "where",
        "while",
    ]
)


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = kotlin_type_map
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        return f"__tmp{self._temp}"

    def _check_keyword(self, name):
        if name in kotlin_keywords:
            return name + "_", True
        if name == "_":
            return self._get_temp(), True
        return name, False

    def visit_Name(self, node):
        node_id, changed = self._check_keyword(node.id)
        if changed:
            return node_id
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
