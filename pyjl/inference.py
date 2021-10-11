import ast
from ctypes import c_int64

from dataclasses import dataclass
from logging import NullHandler
from typing import List, cast, Set, Optional

from py2many.inference import InferTypesTransformer, get_inferred_type, is_compatible
from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node, unparse
from py2many.astx import LifeTime
from py2many.clike import CLikeTranspiler, class_for_typename
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.tracer import is_enum
from pyjl.plugins import CONTAINER_TYPE_MAP, INTEGER_TYPES, JULIA_TYPE_MAP, NUM_TYPES

VARIABLE_TYPES = {}   

#########################################################

def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)

def map_type(typename) :
    typeclass = class_for_typename(typename, "Any")
    if typeclass in JULIA_TYPE_MAP:
        return JULIA_TYPE_MAP[typeclass]
    if typename in CONTAINER_TYPE_MAP:
        return CONTAINER_TYPE_MAP[typename]
    return typename

def get_inferred_julia_type(node):
    if hasattr(node, "julia_annotation"):
        return node.julia_annotation
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition and definition != node:
            return get_inferred_julia_type(definition)
    
    python_type = get_inferred_type(node)
    ret = map_type(get_id(python_type))
    node.julia_annotation = ret
    return ret

def add_julia_annotation(node, left_default, right_default) :
    scope = node.scopes[-1].name
    node.left.julia_annotation = map_type(left_default)
    node.right.julia_annotation = map_type(right_default)
    key_right = (get_id(node.right), scope)
    key_left = (get_id(node.left), scope)
    if(key_left in VARIABLE_TYPES):
        node.left.julia_annotation = VARIABLE_TYPES[key_left]
    if(key_right in VARIABLE_TYPES):
        node.right.julia_annotation = VARIABLE_TYPES[key_right]

def add_julia_type(node, annotation, target):
    julia_annotation = get_inferred_julia_type(node)
    type = map_type(get_id(annotation)) if julia_annotation == None else julia_annotation
    add_julia_variable_type(node, target, type)

def add_julia_variable_type(node, target, annotation):
    # if target (a.k.a node name) is not mapped, map it with corresponding value type
    scope = node.scopes[-1].name
    target_id = get_id(target)
    key = (target_id, scope)
    if(key in VARIABLE_TYPES and VARIABLE_TYPES[key] != annotation):
        raise AstIncompatibleAssign(f"{annotation} incompatible with {VARIABLE_TYPES[key]}", node)
    VARIABLE_TYPES[key] = map_type(annotation)

#########################################################

class InferJuliaTypesTransformer(ast.NodeTransformer):
    """
    Implements Julia type inference logic
    """

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_LIST
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def __init__(self):
        super().__init__()
        self._clike = CLikeTranspiler()

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

    def visit_Return(self, node):
        self.generic_visit(node)
        new_type_str = (
            map_type(get_id(node.value.annotation) if hasattr(node.value, "annotation") else None) 
        )
        if new_type_str is None:
            return node
        for scope in node.scopes:
            type_str = None
            if isinstance(scope, ast.FunctionDef):
                type_str = map_type(get_id(scope.returns))
                if type_str is not None:
                    left_jl_annotation = node.value.left.julia_annotation if hasattr(node.value.left, "julia_annotation") else None
                    right_jl_annotation = node.value.right.julia_annotation if hasattr(node.value.right, "julia_annotation") else None
                    if(((isinstance(node.value.left, ast.Num) or left_jl_annotation in NUM_TYPES) 
                            and right_jl_annotation == "String") 
                            or ((isinstance(node.value.right, ast.Num) or right_jl_annotation in NUM_TYPES) 
                            and left_jl_annotation == "String") ):
                        print("visit_Return - PyJl")
                        type_str = "String"
                    elif new_type_str != type_str:
                        type_str = f"Union{'{'}{type_str},{new_type_str}{'}'}"
                    scope.returns.id = type_str
                    print(ast.dump(node.scopes[1], indent=4))
                else:
                    # Do not overwrite source annotation with inferred
                    if scope.returns is None:
                        scope.returns = ast.Name(id=new_type_str)
                        lifetime = getattr(node.value.annotation, "lifetime", None)
                        if lifetime is not None:
                            scope.returns.lifetime = lifetime
        return node

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)
        self.visit(node.value)

        # TODO: Investigate this better
        ann = getattr(node.value, "annotation", None)
        annotation = ann if ann else getattr(node, "annotation", None)
        if annotation is None:
            return node

        for target in node.targets:
            target_has_annotation = hasattr(target, "annotation")
            inferred = (
                getattr(target.annotation, "inferred", False)
                if target_has_annotation
                else False
            )
            if not target_has_annotation or inferred:
                add_julia_type(node, annotation, target)
                target.annotation = annotation
                target.annotation.inferred = True
        # TODO: Call is_compatible to check if the inferred and user provided annotations conflict
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        self.generic_visit(node)

        # annotation = getattr(node.value, "annotation", None) # why was it node.value?
        # TODO: Investigate this better
        ann = getattr(node.value, "annotation", None)
        annotation = ann if ann else getattr(node, "annotation", None)
        node.annotation = annotation
        node.target.annotation = node.annotation

        target = node.target
        target_typename = self._clike._typename_from_annotation(target)
        if target_typename in self.FIXED_WIDTH_INTS_NAME:
            self.has_fixed_width_ints = True
        # annotation = get_inferred_julia_type(map_type(get_id(node.annotation))) # Does not appear to work
        add_julia_type(node, annotation, target)

        value_typename = self._clike._generic_typename_from_type_node(annotation)
        target_class = class_for_typename(target_typename, None)
        value_class = class_for_typename(value_typename, None)
        if (
            not is_compatible(target_class, value_class, target, node.value)
            and target_class != None
        ):
            raise AstIncompatibleAssign(
                f"{target_class} incompatible with {value_class}", node
            )
        return node

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

        # If one or more nodes are None, skip other conditions
        if ((left is None and right is not None) 
                or (right is None and left is not None)
                or (right is None and left is None)):
            add_julia_annotation(node, get_id(left), get_id(right))
            return node

        # Both operands are annotated
        left_id = get_id(left)
        right_id = get_id(right)

        if left_id == "int":
            left_id = "c_int32"
        if right_id == "int":
            right_id = "c_int32"

        if (left_id in self.FIXED_WIDTH_INTS_NAME
                and right_id in self.FIXED_WIDTH_INTS_NAME):
            ret = self._handle_overflow(node.op, left_id, right_id)
            add_julia_annotation(node, ret, ret)
            return node

        if left_id == right_id:
            # Cover division with ints
            left_annotation = (node.left.julia_annotation 
                if hasattr(node.left, "julia_annotation") else map_type(left_id))
            right_annotation = (node.right.julia_annotation 
                if hasattr(node.right, "julia_annotation") else map_type(right_id))
            if ((isinstance(node.left, ast.Num) or left_annotation in NUM_TYPES) and 
                    (isinstance(node.right, ast.Num) or right_annotation in NUM_TYPES)) :
                if (not isinstance(node.op, ast.Div) or 
                        getattr(node, "use_integer_div", False)):
                    node.annotation = left_id
                    add_julia_annotation(node, left_id, left_id)
                else:
                    node.annotation = "float"
                    add_julia_annotation(node, "float", "float")
                return node
        else:
            if ((left in INTEGER_TYPES and right == "float") or 
                    (right in INTEGER_TYPES and left == "float")):
                add_julia_annotation(node, "float", "float")
                return node
            if (left_id, right_id) in { 
                ("int", "complex"),
                ("complex", "int"),
                ("float", "complex"),
                ("complex", "float"),
            }:
                add_julia_annotation(node, "complex", "complex")
                return node

        mapped_left = map_type(left_id)
        mapped_right = map_type(right_id)
        if ((mapped_left in NUM_TYPES and mapped_right == "String") 
            or (mapped_right in NUM_TYPES and mapped_left == "String")):
            node.annotation = ast.Name(id="str")
        # By default (if no translation possible), the types are left_id and right_id respectively
        add_julia_annotation(node, left_id, right_id)

        ILLEGAL_COMBINATIONS = {}

        if left_id is not None and right_id is not None and (left_id, right_id, type(node.op)) in ILLEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)
        return node

    # def visit_FunctionDef(self, node) -> str:
    #     attr = "annotation"
    #     if hasattr(node, attr):  
    #         type_node = getattr(node, attr)
    #         node.julia_annotation = map_type(CLikeTranspiler._typename_from_type_node(type_node)) # Wrong use of CLikeTranspiler
    #     return node


