import ast
from ctypes import (
    c_int8,
    c_int16,
    c_int32,
    c_int64,
    c_uint8,
    c_uint16,
    c_uint32,
    c_uint64,
)
from typing import Dict, List

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler
from py2many.inference import InferTypesTransformer, LanguageInferenceBase

V_TYPE_MAP: Dict[type, str] = {
    int: "int",
    float: "f64",
    bytes: "[]u8",
    str: "string",
    bool: "bool",
    list: "[]Any",
    List: "[]Any",
    c_int8: "i8",
    c_int16: "i16",
    c_int32: "int",
    c_int64: "i64",
    c_uint8: "u8",
    c_uint16: "u16",
    c_uint32: "u32",
    c_uint64: "u64",
}

V_CONTAINER_TYPE_MAP = {
    "List": "[]",
    "list": "[]",
    "Dict": "map",
    "dict": "map",
    "Set": "set",
    "set": "set",
    "Optional": "?",
}

V_WIDTH_RANK = {
    "bool": 0,
    "i8": 1,
    "byte": 2,
    "u8": 2,
    "i16": 3,
    "u16": 4,
    "int": 5,
    "u32": 6,
    "i64": 7,
    "u64": 8,
    "f32": 9,
    "f64": 10,
}


class VInference(LanguageInferenceBase):
    TYPE_MAP = V_TYPE_MAP
    CONTAINER_TYPE_MAP = V_CONTAINER_TYPE_MAP
    WIDTH_RANK = V_WIDTH_RANK


def get_inferred_v_type(node):
    return VInference.get_inferred_language_type(node, "v_annotation")


class InferVTypesTransformer(InferTypesTransformer):
    """Implements v type inference logic as opposed to python type inference logic"""

    @staticmethod
    def _numeric_binop_arg_names(node: ast.AST) -> set[str]:
        arg_names: set[str] = set()
        for child in ast.walk(node):
            if not isinstance(child, ast.BinOp):
                continue
            left_is_name = isinstance(child.left, ast.Name)
            right_is_name = isinstance(child.right, ast.Name)
            left_is_number = isinstance(child.left, ast.Constant) and isinstance(
                child.left.value, (int, float)
            )
            right_is_number = isinstance(child.right, ast.Constant) and isinstance(
                child.right.value, (int, float)
            )
            if left_is_name and right_is_number:
                arg_names.add(child.left.id)
            if right_is_name and left_is_number:
                arg_names.add(child.right.id)
        return arg_names

    @staticmethod
    def _callable_type_parts(node: ast.Lambda):
        callable_type = getattr(node, "callable_type", None)
        if not (
            callable_type
            and isinstance(callable_type, ast.Subscript)
            and isinstance(callable_type.slice, ast.Tuple)
            and len(callable_type.slice.elts) == 2
        ):
            return [], None

        args_node, ret_node = callable_type.slice.elts
        arg_types = []
        if isinstance(args_node, ast.List):
            arg_types = [
                CLikeTranspiler._generic_typename_from_type_node(e)
                for e in args_node.elts
            ]
        return arg_types, CLikeTranspiler._generic_typename_from_type_node(ret_node)

    @staticmethod
    def _set_arg_type(node: ast.arg, typename: str) -> None:
        node.v_annotation = typename
        if not getattr(node, "annotation", None):
            node.annotation = ast.Name(id=typename)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        if isinstance(node.value, ast.Lambda):
            node.value.callable_type = node.annotation
        return super().visit_AnnAssign(node)

    def visit_Call(self, node: ast.Call) -> ast.AST:
        self.generic_visit(node)
        if get_inferred_v_type(node) == "Any":
            node.v_needs_any_to_string = True
        return node

    def visit_Lambda(self, node: ast.Lambda) -> ast.AST:
        numeric_arg_names = self._numeric_binop_arg_names(node.body)
        explicit_arg_types, explicit_ret_type = self._callable_type_parts(node)
        for i, arg in enumerate(node.args.args):
            if i < len(explicit_arg_types):
                self._set_arg_type(arg, explicit_arg_types[i])
            elif arg.arg in numeric_arg_names:
                self._set_arg_type(arg, "int")

        self.generic_visit(node)

        ret_type = get_inferred_v_type(node.body)
        if (
            (not ret_type or ret_type == "Any")
            and isinstance(node.body, ast.BinOp)
            and numeric_arg_names
        ):
            ret_type = "int"
            node.body.v_annotation = ret_type
        if not ret_type and explicit_ret_type:
            ret_type = explicit_ret_type
        if ret_type:
            node.v_annotation = ret_type
        if ret_type == "Any":
            node.v_needs_any_to_string = True
        return node

    def _handle_overflow(self, op, left_id, right_id):
        return VInference.handle_overflow(op, left_id, right_id)

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
            node.v_annotation = get_inferred_v_type(right)
            return node

        if right is None and left is not None:
            node.v_annotation = get_inferred_v_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.v_annotation = ret
        return node


def infer_v_types(node):
    visitor = InferVTypesTransformer()
    visitor.visit(node)
