import ast

from common.clike import CLikeTranspiler as CommonCLikeTranspiler


dart_type_map = {
    "bool": "bool",
    "int": "int",
    "float": "double",
    "bytes": "Uint8List",
    "str": "String",
}

# allowed as names in Python but treated as keywords in Dart
dart_keywords = frozenset(
    [
        "assert",
        "break",
        "case",
        "catch",
        "class",
        "const",
        "continue",
        "default",
        "do",
        "else",
        "enum",
        "extends",
        "false",
        "final",
        "finally",
        "for",
        "if",
        "in",
        "is",
        "new",
        "null",
        "rethrow",
        "return",
        "super",
        "switch",
        "this",
        "throw",
        "true",
        "try",
        "var",
        "void",
        "while",
        "with",
    ]
)


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        self._type_map = dart_type_map

    def visit_Name(self, node):
        if node.id in dart_keywords:
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
