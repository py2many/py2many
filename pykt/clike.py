import ast

from common.clike import CLikeTranspiler as CommonCLikeTranspiler


kotlin_type_map = {
    "bool": "Boolean",
    "int": "Int",
    "float": "Double",
    "bytes": "ByteArray",
    "str": "String",
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
        self._type_map = kotlin_type_map

    def visit_Name(self, node):
        if node.id in kotlin_keywords:
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
        return "{0}.any({1})".format(right, left)
