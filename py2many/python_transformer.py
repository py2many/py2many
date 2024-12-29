import ast

from .ast_helpers import create_ast_node
from .clike import CLikeTranspiler


class RestoreMainRewriter(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        is_python_main = getattr(node, "python_main", False)

        if is_python_main:
            if_block = create_ast_node("if __name__ == '__main__': True", node)
            if_block.body = node.body
            ast.fix_missing_locations(if_block)
            return if_block
        return node


class PythonTranspiler(CLikeTranspiler):
    NAME = "python"

    def __init__(self):
        super().__init__()
        CLikeTranspiler._type_map = {}
        CLikeTranspiler._container_type_map = {}

    def visit(self, node):
        return ast.unparse(node)

    def usings(self):
        return "\n".join(
            [
                "from typing import Callable, Dict, List, Set, Optional",
                "from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64",
                "from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64",
                "import sys",
            ]
        )
