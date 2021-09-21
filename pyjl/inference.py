import ast

from dataclasses import dataclass
from typing import cast, Set, Optional

from py2many.inference import InferTypesTransformer, get_inferred_type, is_compatible
from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node, unparse
from py2many.astx import LifeTime
from py2many.clike import CLikeTranspiler, class_for_typename
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.tracer import is_enum
from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64

JULIA_TYPE_MAP = {
    bool: "Bool",
    int: "Int64",
    float: "Float64",
    bytes: "Array{UInt8}",
    str: "String",
    c_int8: "Int8",
    c_int16: "Int16",
    c_int32: "Int32",
    c_int64: "Int64",
    c_uint8: "UInt8",
    c_uint16: "UInt16",
    c_uint32: "UInt32",
    c_uint64: "UInt64",
}

INTEGER_TYPES = (
    [
        "Int64", 
        "Int32", 
        "UInt128", 
        "Uint64", 
        "Uint32", 
        "Uint16", 
        "UInt8", 
        "Integer"
    ]
)

NUM_TYPES = INTEGER_TYPES + ["Float64"]

class InferJuliaTypesTransformer(ast.NodeTransformer):
    """
    Implements Julia type inference logic
    """

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

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
                    # Do not overwrite source annotation with inferred
                    if scope.returns is None:
                        scope.returns = ast.Name(id=new_type_str)
                        lifetime = getattr(node.value.annotation, "lifetime", None)
                        if lifetime is not None:
                            scope.returns.lifetime = lifetime
        return node

    def _handle_overflow(self, op, left_id, right_id):
        widening_op = isinstance(op, ast.Add) or isinstance(op, ast.Mult)
        left_class = class_for_typename(left_id, None)
        right_class = class_for_typename(right_id, None)
        left_idx = (
            self.FIXED_WIDTH_INTS_LIST.index(left_class)
            if left_class in self.FIXED_WIDTH_INTS
            else -1
        )
        right_idx = (
            self.FIXED_WIDTH_INTS_LIST.index(right_class)
            if right_class in self.FIXED_WIDTH_INTS
            else -1
        )
        max_idx = max(left_idx, right_idx)
        cint64_idx = self.FIXED_WIDTH_INTS_LIST.index(c_int64)
        if widening_op:
            if max_idx not in {-1, cint64_idx, len(self.FIXED_WIDTH_INTS_LIST) - 1}:
                # i8 + i8 => i16 for example
                return self.FIXED_WIDTH_INTS_NAME_LIST[max_idx + 1]
        if left_id == "float" or right_id == "float":
            return "float"
        return left_id if left_idx > right_idx else right_id

    ######################################################
    ###################### Modified ######################
    ######################################################

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
            # node.annotation = right
            node.julia_annotation = map_type(get_id(right))
            return node

        if right is None and left is not None:
            # node.annotation = left
            node.julia_annotation = map_type(get_id(left))
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        if left_id == right_id and left_id == "int":
            if not isinstance(node.op, ast.Div) or getattr(
                node, "use_integer_div", False
            ):
                # node.annotation = left
                node.julia_annotation = map_type(get_id(left))
            else:
                # node.annotation = ast.Name(id="float")
                node.julia_annotation = map_type("float")
            return node

        if left_id == "int":
            left_id = "c_int32"
        if right_id == "int":
            right_id = "c_int32"

        if (
            left_id in self.FIXED_WIDTH_INTS_NAME
            and right_id in self.FIXED_WIDTH_INTS_NAME
        ):
            ret = self._handle_overflow(node.op, left_id, right_id)
            # node.annotation = ast.Name(id=ret)
            node.julia_annotation = ret
            return node
        if left_id == right_id:
            # Exceptions: division operator
            # if isinstance(node.op, ast.Div):
            #     if left_id == "int":
            #         node.annotation = ast.Name(id="float")
            #         return node
            # node.annotation = left
            node.julia_annotation = map_type("float")
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                # node.annotation = ast.Name(id="float")
                node.julia_annotation = map_type("float")
                return node
            # TODO: review complex
            if (left_id, right_id) in { 
                ("int", "complex"),
                ("complex", "int"),
                ("float", "complex"),
                ("complex", "float"),
            }:
                node.annotation = ast.Name(id="complex")
                return node

        # Container multiplication
        # if isinstance(node.op, ast.Mult) and {left_id, right_id} in [
        #     {"bytes", "int"},
        #     {"str", "int"},
        #     {"tuple", "int"},
        #     {"List", "int"},
        # ]:
        #     node.annotation = ast.Name(id=left_id)
        #     return node

        # TODO: Check for legal combinations in Julia
        # LEGAL_COMBINATIONS = {("str", ast.Mod), ("List", ast.Add), ("int", ast.Add)}

        # if left_id is not None and (left_id, type(node.op)) not in LEGAL_COMBINATIONS:
        #     raise AstUnrecognisedBinOp(left_id, right_id, node)

        return node

def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)

def map_type(typename) :
    typeclass = class_for_typename(typename, "Any")
    if typeclass in JULIA_TYPE_MAP:
        return JULIA_TYPE_MAP[typeclass]
    return typename
