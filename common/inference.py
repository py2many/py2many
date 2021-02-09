import ast
import copy
import re

from dataclasses import dataclass
from common.analysis import get_id
from ctypes import c_int, c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64


@dataclass
class InferMeta:
    has_fixed_width_ints: bool


def infer_types(node) -> InferMeta:
    visitor = InferTypesTransformer()
    visitor.visit(node)
    return InferMeta(visitor.has_fixed_width_ints)


class InferTypesTransformer(ast.NodeTransformer):
    """
    Tries to infer types
    """

    TYPE_DICT = {int: "int", float: "float", str: "str"}
    FIXED_WIDTH_INTS = {
        c_int8,
        c_int16,
        c_int32,
        c_int64,
        c_uint8,
        c_uint16,
        c_uint32,
        c_uint64,
    }
    FIXED_WIDTH_INTS_NAME_LIST = [
        "c_int8",
        "c_int16",
        "c_int32",
        "c_int64",
        "c_uint8",
        "c_uint16",
        "c_uint32",
        "c_uint64",
    ]
    FIXED_WIDTH_INTS_NAME = set(FIXED_WIDTH_INTS_NAME_LIST)

    def __init__(self):
        self.handling_annotation = False
        self.has_fixed_width_ints = False

    def visit_NameConstant(self, node):
        t = type(node.value)
        if t in self.TYPE_DICT:
            node.annotation = ast.Name(id=self.TYPE_DICT[t])
        elif t in self.FIXED_WIDTH_INTS:
            node.annotation = ast.Name(id=str(t))
        elif t != type(None):
            raise (Exception(f"{t} not found in TYPE_DICT"))

        self.generic_visit(node)
        return node

    def visit_Constant(self, node):
        return self.visit_NameConstant(node)

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)

        target = node.targets[0]
        if hasattr(node.value, "annotation"):
            target.annotation = node.value.annotation
        else:
            var = node.scopes.find(get_id(node.value))

            if var and hasattr(var, "annotation"):
                target.annotation = copy.copy(var.annotation)

        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        self.generic_visit(node)

        node.target.annotation = node.annotation
        if get_id(node.annotation) in self.FIXED_WIDTH_INTS_NAME:
            self.has_fixed_width_ints = True
        return node

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.AST:
        self.generic_visit(node)

        target = node.target
        if hasattr(node.value, "annotation"):
            target.annotation = node.value.annotation

        return node

    def visit_Return(self, node):
        self.generic_visit(node)
        new_type_str = (
            get_id(node.value.annotation) if hasattr(node.value, "annotation") else None
        )
        if new_type_str is None:
            return node
        for scope in node.scopes:
            type_str = None
            if isinstance(scope, ast.FunctionDef):
                type_str = get_id(scope.returns)
                if type_str is not None:
                    if new_type_str != type_str:
                        type_str = f"Union[{type_str},{new_type_str}]"
                        scope.returns.id = type_str
                else:
                    scope.returns = ast.Name(id=new_type_str)
        return node

    def visit_UnaryOp(self, node):
        self.generic_visit(node)

        if isinstance(node.operand, ast.Name):
            operand = node.scopes.find(get_id(node.operand))
        else:
            operand = node.operand

        if hasattr(operand, "annotation"):
            node.annotation = operand.annotation

        return node

    def _handle_overflow(self, op, left_id, right_id):
        widening_op = isinstance(op, ast.Add) or isinstance(op, ast.Mult)
        left_idx = self.FIXED_WIDTH_INTS_NAME_LIST.index(left_id) if left_id in self.FIXED_WIDTH_INTS_NAME else -1
        right_idx = self.FIXED_WIDTH_INTS_NAME_LIST.index(right_id) if right_id in self.FIXED_WIDTH_INTS_NAME else -1
        max_idx = max(left_idx, right_idx)
        cint64_idx = self.FIXED_WIDTH_INTS_NAME_LIST.index("c_int64")
        if widening_op:
            if max_idx not in {-1, cint64_idx, len(self.FIXED_WIDTH_INTS_NAME_LIST)-1}:
                # i8 + i8 => i16 for example
                return self.FIXED_WIDTH_INTS_NAME_LIST[max_idx+1]
        if left_id == "float" or right_id == "float":
            return "float"
        return left_id if left_idx > right_idx else right_id

    def visit_BinOp(self, node):
        self.generic_visit(node)

        if isinstance(node.left, ast.Name):
            lvar = node.scopes.find(get_id(node.left))
        else:
            lvar = node.left

        if isinstance(node.right, ast.Name):
            rvar = node.scopes.find(get_id(node.right))
        else:
            rvar = node.right

        left = lvar.annotation if lvar and hasattr(lvar, "annotation") else None
        right = rvar.annotation if rvar and hasattr(rvar, "annotation") else None

        if left is None and right is not None:
            node.annotation = right
            return node

        if right is None and left is not None:
            node.annotation = left
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        if (
            left_id in self.FIXED_WIDTH_INTS_NAME
            and right_id in self.FIXED_WIDTH_INTS_NAME
        ):
            ret = self._handle_overflow(node.op, left_id, right_id)
            node.annotation = ast.Name(id=ret)
            return node
        if left_id == right_id:
            # Exceptions: division operator
            if isinstance(node.op, ast.Div):
                if left_id == "int":
                    node.annotation = ast.Name(id="float")
                    return node
            node.annotation = copy.copy(left)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.annotation = ast.Name(id="float")
                return node

            raise Exception(f"type error: {left_id} {type(node.op)} {right_id}")

        return node
