import ast

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler

py14_type_map = {
    "bool": "bool",
    "int": "int",
    "float": "double",
    "bytes": "byte[]",
    "str": "std::string",
    "c_int8": "int8_t",
    "c_int16": "int16_t",
    "c_int32": "int32_t",
    "c_int64": "int64_t",
    "c_uint8": "uint8_t",
    "c_uint16": "uint16_t",
    "c_uint32": "uint32_t",
    "c_uint64": "uint64_t",
}


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = py14_type_map

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Pow):
            return "std::pow({0}, {1})".format(
                self.visit(node.left), self.visit(node.right)
            )
        left = self.visit(node.left)
        if not isinstance(node.left, ast.Name) and not isinstance(
            node.left, ast.Constant
        ):
            left = f"({left})"
        right = self.visit(node.right)
        if not isinstance(node.right, ast.Name) and not isinstance(
            node.right, ast.Constant
        ):
            right = f"({right})"
        return " ".join([left, self.visit(node.op), right])

    def visit_In(self, node):
        self._headers.append("#include <algorithm>")
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"(std::find({right}.begin(), {right}.end(), {left}) != {right}.end())"
