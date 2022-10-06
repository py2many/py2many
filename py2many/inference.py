import argparse
import ast

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64
from dataclasses import dataclass
import math
import re
from typing import Any, Dict, List, Tuple, cast, Set, Optional

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node, unparse
from py2many.astx import LifeTime
from py2many.clike import CLikeTranspiler, class_for_typename
from py2many.exceptions import AstIncompatibleAssign
from py2many.tracer import find_node_by_type, find_parent_of_type, is_enum

try:
    from typpete.inference_runner import infer as infer_types_ast
    from typpete.src.context import Context
    from typpete.src.z3_types import TypesSolver
except ModuleNotFoundError:

    def infer_types_ast(node):
        return node


@dataclass
class InferMeta:
    has_fixed_width_ints: bool


def infer_types(node) -> InferMeta:
    visitor = InferTypesTransformer()
    visitor.visit(node)
    return InferMeta(visitor.has_fixed_width_ints)


def add_is_annotation(node):
    return AnnotationVisitor().visit(node)


def infer_types_typpete(node) -> InferMeta:
    solver = TypesSolver(node)
    context = Context(node, node.body, solver)
    for stmt in node.body:
        infer_types_ast(stmt, context, solver)

    solver.push()

    return InferMeta(True)


def get_inferred_type(node):
    if hasattr(node, "annotation"):
        return node.annotation
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node and definition is not None:
            return get_inferred_type(definition)
    elif isinstance(node, ast.Constant) or isinstance(node, ast.NameConstant):
        return InferTypesTransformer._infer_primitive(node.value)
    return None


def is_reference(arg):
    annotation_has_ref = hasattr(arg, "annotation") and isinstance(
        arg.annotation, ast.Subscript
    )
    if annotation_has_ref:
        return True
    inferred = get_inferred_type(arg)
    annotation_has_ref = hasattr(inferred, "id") and isinstance(
        inferred.id, ast.Subscript
    )
    return annotation_has_ref


def bit_length(val: ast.AST) -> int:
    if isinstance(val, ast.Constant) and isinstance(val.value, int):
        return int.bit_length(val.value)
    return 0


def is_compatible(
    cls1, cls2, target: Optional[ast.AST] = None, source: Optional[ast.AST] = None
):
    """This needs to return true if narrowing one of the classes leads to the other class"""
    # For now, handle fixed width only. In the future look into List[int] vs List
    fixed_width = InferTypesTransformer.FIXED_WIDTH_INTS
    fixed_width_bit_length = InferTypesTransformer.FIXED_WIDTH_BIT_LENGTH
    if cls1 in fixed_width and (cls2 in fixed_width or cls2 is int):
        target_bit_length = fixed_width_bit_length[cls1]
        source_bit_length = fixed_width_bit_length[cls2]
        # Sometimes we have more information about the actual bit length
        # For example 100 is of type int, which maps to i32 on many target platforms, but has
        # an actual bit length of 7
        source_value_bit_length = bit_length(source) if source is not None else 0
        if source_value_bit_length:
            source_bit_length = source_value_bit_length
        return target_bit_length >= source_bit_length
    return True


class FuncTypeDispatch():
    def visit_zip(self, node, vargs, kwargs):
        ann_ids = []
        for arg in node.args:
            arg_id = get_id(arg)
            if isinstance(arg, ast.Attribute) and get_id(arg.value) == "self":
                class_scope = find_node_by_type(ast.ClassDef, node.scopes)
                if class_scope:
                    attr_node = class_scope.scopes.find(arg.attr)
                    if hasattr(attr_node, "target_node"):
                        ann = getattr(attr_node.target_node, 'annotation', None)
            else:
                ann = getattr(node.scopes.find(arg_id), 'annotation', None)
            if ann:
                ann_ids.append(unparse(ann))
            else:
                ann_ids.append("Any")
        
        return f"({', '.join(ann_ids)})"

    def visit_min_max(self, node, vargs, kwargs):
        if vargs and (node_type := get_inferred_type(vargs[0])):
            return ast.unparse(node_type)
        return None

    def visit_iter(self, node, vargs, kwargs):
        node_type = get_inferred_type(vargs[0])
        if node_type:
            return ast.unparse(node_type)
        return None

    def visit_next(self, node, vargs, kwargs):
        node_type = get_inferred_type(vargs[0])
        if isinstance(node_type, ast.Subscript):
            return ast.unparse(node_type.slice)
        return None

class AnnotationVisitor(ast.NodeTransformer):
    """Add _is_annotation attribute to all annotations"""
    def __init__(self) -> None:
        super().__init__()
        self._is_annotation = False

    def visit(self, node: ast.AST) -> Any:
        if getattr(node, "annotation", None):
            node.annotation.is_annotation = True
            super().visit(node.annotation)
        super().visit(node)
        return node

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self.generic_visit(node)
        if getattr(node, "is_annotation", False):
            node.value.is_annotation = True
            node.slice.is_annotation = True
        return node

    def visit_List(self, node: ast.List) -> Any:
        self.generic_visit(node)
        if getattr(node, "is_annotation", False):
            for n in node.elts:
                n.is_annotation = True
        return node
    
    def visit_Tuple(self, node: ast.Tuple) -> Any:
        self.generic_visit(node)
        if getattr(node, "is_annotation", False):
            for n in node.elts:
                n.is_annotation = True
        return node

# TODO: Cross-Module support
_class_attribute_types = {}

class InferTypesTransformer(ast.NodeTransformer):
    """
    Tries to infer types
    """

    # TODO: Change to use typeshed (https://github.com/python/typeshed)
    FUNC_TYPE_MAP = {
        len: lambda self, node, vargs, kwargs: "int",
        math.sqrt: lambda self, node, vargs, kwargs: "float",
        range: lambda self, node, vargs, kwargs: "int",
        str.encode: lambda self, node, vargs, kwargs: "bytes",
        str.format: lambda self, node, vargs, kwargs: "str",
        str.lower: lambda self, node, vargs, kwargs: "str",
        str.replace: lambda self, node, vargs, kwargs: "str",
        bytes.translate: lambda self, node, vargs, kwargs: "bytes",
        bytearray.translate: lambda self, node, vargs, kwargs: "bytearray",
        argparse.ArgumentParser: lambda self, node, vargs, kwargs: "argparse.ArgumentParser",
        isinstance: lambda self, node, vargs, kwargs: "bool",
        zip: FuncTypeDispatch.visit_zip,
        max: FuncTypeDispatch.visit_min_max,
        min: FuncTypeDispatch.visit_min_max,
        iter: FuncTypeDispatch.visit_iter,
        next: FuncTypeDispatch.visit_next,
    }
    TYPE_DICT = {
        int: "int",
        float: "float",
        str: "str",
        bool: "bool",
        bytes: "bytes",
        complex: "complex",
        type(...): "...",
    }
    CONTAINER_TYPE_DICT = {
        list: "list",
        List: "List",
        Dict: "Dict",
        Set: "Set",
        Tuple: "Tuple",
        tuple: "tuple",
        Optional: "Optional",
        bytearray: f"bytearray",
    }
    FIXED_WIDTH_INTS_LIST = [
        bool,
        c_int8,
        c_int16,
        c_int32,
        c_int64,
        c_uint8,
        c_uint16,
        c_uint32,
        c_uint64,
    ]
    FIXED_WIDTH_INTS = set(FIXED_WIDTH_INTS_LIST)
    FIXED_WIDTH_BIT_LENGTH = {
        bool: 1,
        c_int8: 7,
        c_uint8: 8,
        c_int16: 15,
        c_uint16: 16,
        # This is based on how int maps to i32 on many platforms
        int: 31,
        c_int32: 31,
        c_uint32: 32,
        c_int64: 63,
        c_uint64: 64,
    }
    # The order needs to match FIXED_WIDTH_INTS_LIST. Extra elements ok.
    FIXED_WIDTH_INTS_NAME_LIST = [
        "bool",
        "c_int8",
        "c_int16",
        "c_int32",
        "c_int64",
        "c_uint8",
        "c_uint16",
        "c_uint32",
        "c_uint64",
        "i8",
        "i16",
        "i32",
        "i64",
        "isize",
        "ilong",
        "u8",
        "u16",
        "u32",
        "u64",
        "usize",
        "ulong",
    ]
    FIXED_WIDTH_INTS_NAME = set(FIXED_WIDTH_INTS_NAME_LIST)

    def __init__(self):
        self.handling_annotation = False
        self.has_fixed_width_ints = False
        # TODO: remove this and make the methods into classmethods
        self._clike = CLikeTranspiler()
        self._imported_names = None
        # Holds annotations for specific blocks
        self._block_annotations = {}
        self._has_generators = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._imported_names = node.imported_names
        self._clike._imported_names = self._imported_names
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node):
        node.annotation = ast.Name(id=node.name)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._has_generators = False
        self.generic_visit(node)
        if self._has_generators:
            node.annotation = ast.Name(id="Generator")

        class_type = find_parent_of_type(ast.ClassDef, node.scopes)
        if len(node.scopes) > 1:
            if class_type and not hasattr(node, "self_type"):
                node.self_type = get_id(class_type)

        if len(node.body) > 0 and isinstance(node.body[-1], ast.Return) and \
                hasattr(node.body[-1], "annotation") and \
                node.returns == None:
            node.returns = node.body[-1].annotation

        if node.name == "__getattr__" and class_type:
            _class_attribute_types[class_type.name] = node.returns

        return node

    @staticmethod
    def _infer_primitive(value) -> Optional[ast.AST]:
        t = type(value)
        annotation = None
        if t in InferTypesTransformer.TYPE_DICT:
            annotation = ast.Name(id=InferTypesTransformer.TYPE_DICT[t])
        elif t in InferTypesTransformer.FIXED_WIDTH_INTS:
            annotation = ast.Name(id=str(t))
        elif t != type(None):
            raise NotImplementedError(f"{t} not found in TYPE_DICT")
        return annotation

    def visit_NameConstant(self, node):
        if node.value is Ellipsis:
            return node
        annotation = self._infer_primitive(node.value)
        if annotation is not None:
            node.annotation = annotation
            node.annotation.lifetime = (
                LifeTime.STATIC if type(node.value) == str else LifeTime.UNKNOWN
            )
        self.generic_visit(node)
        return node

    def visit_Name(self, node):
        annotation = get_inferred_type(node)
        if annotation is not None:
            node.annotation = annotation
        if node.id in self._block_annotations:
            node.annotation = self._block_annotations[node.id]
        return node

    def visit_Constant(self, node):
        return self.visit_NameConstant(node)

    @staticmethod
    def _annotate(node, typename: str):
        # ast.parse produces a Module object that needs to be destructured
        type_annotation = cast(ast.Expr, create_ast_node(typename, node)).value
        node.annotation = type_annotation
        node.annotation.is_annotation = True

    def visit_List(self, node):
        self.generic_visit(node)
        self._visit_container_type(node, typename="List")
        return node

    def visit_Tuple(self, node: ast.Tuple) -> Any:
        self.generic_visit(node)
        self._visit_container_type(node, typename="Tuple")
        return node

    def _visit_container_type(self, node, typename="Any"):
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            if getattr(node, "is_annotation", False):
                return node
            else:
                self._visit_container_elem_types(node, typename=typename)
        else:
            if not hasattr(node, "annotation"):
                node.annotation = ast.Name(id=typename)

    def _visit_container_elem_types(self, node, typename = "Any"):
        if elements := node.elts:
            elt_types: Set[str] = set()
            for e in elements:
                typ = get_inferred_type(e)
                if typ is not None:
                    elt_types.add(unparse(typ))

            if len(elt_types) == 0:
                node.annotation = ast.Name(id=typename)
            elif len(elt_types) == 1:
                self._annotate(node, f"{typename}[{elt_types.pop()}]")
            elif len(elt_types) == 2:
                # Promotion
                elt_1 = elt_types.pop()
                elt_2 = elt_types.pop()
                if (elt_1 == "int" and elt_2 == "float") or \
                        (elt_2 == "int" and elt_1 == "float"):
                    self._annotate(node, f"{typename}[float]")


    def visit_Set(self, node):
        self.generic_visit(node)
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            elt_types = set([get_id(get_inferred_type(e)) for e in elements])
            if len(elt_types) == 1:
                if hasattr(elements[0], "annotation"):
                    elt_type = get_id(elements[0].annotation)
                    self._annotate(node, f"Set[{elt_type}]")
                    return node
        if not hasattr(node, "annotation"):
            node.annotation = ast.Name(id="Set")
        return node

    def visit_Dict(self, node):
        self.generic_visit(node)
        if len(node.keys) > 0:

            def typename(e):
                get_inferred_type(e)  # populates e.annotation
                return self._clike._generic_typename_from_annotation(e)

            key_types = set([typename(e) for e in node.keys])
            only_key_type = next(iter(key_types))
            if only_key_type == None:
                only_key_type = "Any"
            if len(key_types) == 1:
                key_type = only_key_type
            else:
                key_type = "Any"
            value_types = set([typename(e) for e in node.values])
            only_value_type = next(iter(value_types))
            if only_value_type == None:
                only_value_type = "Any"
            if len(value_types) == 1:
                value_type = only_value_type
            else:
                value_type = "Any"
            if key_type == "Any" and value_type == "Any":
                self._annotate(node, f"Dict")
            else:
                self._annotate(node, f"Dict[{key_type}, {value_type}]")
            lifetimes = set(
                [
                    getattr(e.annotation, "lifetime", None)
                    for e in node.values
                    if hasattr(e, "annotation")
                ]
            )
            only_lifetime = next(iter(lifetimes)) if len(lifetimes) == 1 else None
            if len(lifetimes) == 1 and only_lifetime != None:
                lifetime = only_lifetime
            else:
                lifetime = LifeTime.UNKNOWN
            node.annotation.lifetime = lifetime
        else:
            if not hasattr(node, "annotation"):
                self._annotate(node, "Dict")
        return node

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)

        if node.type_comment:
            # Propagate type-comment
            annotation = ast.Name(id = node.type_comment)
            node.value.type_comment = node.type_comment
        else:
            annotation = getattr(node.value, "annotation", None)

        if not annotation:
            # Attempt to get type
            if isinstance(node.value, ast.Call):
                if typename := getattr(node.value, "annotation", None):
                    annotation = typename
                else:
                    func_node = node.scopes.find(get_id(node.value.func))
                    if id_type := getattr(func_node, "annotation", None):
                        annotation = id_type
                    else:
                        return node

            elif isinstance(node.value, ast.Name):
                # Try to get related assignment
                assign_ann = self._find_annotated_assign(node.value)
                if assign_ann:
                    annotation = assign_ann
                else: 
                    return node
            else:
                return node


        for target in node.targets:
            target_has_annotation = hasattr(target, "annotation")
            inferred = (
                getattr(target.annotation, "inferred", False)
                if target_has_annotation
                else False
            )
            if (not target_has_annotation or inferred):
                if isinstance(target, ast.Attribute) and \
                        (attr_lst := get_id(target).split(".")):
                    if attr_lst[0] == "self":
                        class_node = find_node_by_type(ast.ClassDef, node.scopes)
                        cls_node = class_node.scopes.find(attr_lst[1])
                        if cls_node and not hasattr(cls_node, "annotation"):
                            cls_node.annotation = annotation
                            cls_node.annotation.inferred = True
                target.annotation = annotation
                target.annotation.inferred = True
        # TODO: Call is_compatible to check if the inferred and user provided annotations conflict
        return node

    def _find_annotated_assign(self, node):
        assign = node.scopes.find(get_id(node))
        if assign:
            if (assign_ann := getattr(assign, "annotation", None)):
                return assign_ann
            else:
                if value := getattr(assign, "value", None):
                    return self._find_annotated_assign(value)
        return None

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        self.generic_visit(node)
        node.target.annotation = node.annotation
        target = node.target
        target_typename = self._clike._typename_from_annotation(target)
        if target_typename in self.FIXED_WIDTH_INTS_NAME:
            self.has_fixed_width_ints = True
        annotation = get_inferred_type(node.value)
        value_typename = self._clike._generic_typename_from_type_node(annotation)
        target_class = class_for_typename(target_typename, None)
        value_class = class_for_typename(value_typename, None)
        if (
            not is_compatible(target_class, value_class, target, node.value)
            and target_class is not None
        ):
            raise AstIncompatibleAssign(
                f"{target_class} incompatible with {value_class}", node
            )
        return node

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.AST:
        self.generic_visit(node)

        target = node.target
        annotation = getattr(node.value, "annotation", None)
        if annotation is not None and not hasattr(target, "annotation"):
            target.annotation = annotation

        return node

    def visit_Compare(self, node):
        self.generic_visit(node)
        node.annotation = ast.Name(id="bool")
        return node

    def visit_Return(self, node):
        self.generic_visit(node)
        new_type_str = (
            get_id(node.value.annotation) if hasattr(node.value, "annotation") else None
        )
        if new_type_str is None:
            return node
        
        # Finds the closest node that is a function definition
        func_node = find_node_by_type(ast.FunctionDef, node.scopes)
        type_str = get_id(func_node.returns) if func_node else None
        if type_str:
            if new_type_str != type_str:
                type_str = f"Union[{type_str},{new_type_str}]"
                func_node.returns.id = type_str
        else:
            # Do not overwrite source annotation with inferred
            if func_node and func_node.returns is None:
                func_node.returns = ast.Name(id=new_type_str)
                lifetime = getattr(node.value.annotation, "lifetime", None)
                if lifetime is not None:
                    func_node.returns.lifetime = lifetime

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

        # If one node is None, skip other conditions
        if left is None or right is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left.value) if isinstance(left, ast.Subscript) else get_id(left)
        right_id = get_id(right.value) if isinstance(right, ast.Subscript) else get_id(right)

        if left_id == right_id and left_id == "int":
            if not isinstance(node.op, ast.Div) or getattr(
                node, "use_integer_div", False
            ):
                node.annotation = left
            else:
                node.annotation = ast.Name(id="float")
            return node

        # Does this hold across all languages?
        if left_id == "int":
            left_id = "c_int32"
        if right_id == "int":
            right_id = "c_int32"

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
            node.annotation = left
            return node

        if left_id in self.FIXED_WIDTH_INTS_NAME:
            left_id = "int"
        if right_id in self.FIXED_WIDTH_INTS_NAME:
            right_id = "int"
        if (left_id, right_id) in {("int", "float"), ("float", "int")}:
            node.annotation = ast.Name(id="float")
            return node
        if (left_id, right_id) in {
            ("int", "complex"),
            ("complex", "int"),
            ("float", "complex"),
            ("complex", "float"),
        }:
            node.annotation = ast.Name(id="complex")
            return node

        if isinstance(node.op, ast.Mult):
            # Container multiplication
            if (left_id, right_id) in [
                    ("bytes", "int"),
                    ("str", "int"),
                    ("tuple", "int"),
                    ("List", "int"),
                    ("int", "bool")]:
                node.annotation = ast.Name(id=left_id)
                return node
            elif (left_id, right_id) in [
                    ("int", "bytes"),
                    ("int", "str"),
                    ("int", "tuple"),
                    ("int", "List"),
                    ("bool", "int")]:
                node.annotation = ast.Name(id=right_id)
                return node

        # LEGAL_COMBINATIONS = {("str", ast.Mod), ("List", ast.Add)}

        # if left_id is not None and (left_id, type(node.op)) not in LEGAL_COMBINATIONS:
        #     raise AstUnrecognisedBinOp(left_id, right_id, node)

        return node

    def visit_Attribute(self, node):
        self.generic_visit(node)
        value_id = get_id(node.value)
        if not getattr(node, "annotation", None):
            if isinstance(node.value, ast.Name):
                val = node.scopes.find(get_id(node.value))
                ann = get_id(getattr(val, "annotation", None))
                if ann in _class_attribute_types:
                    node.annotation = _class_attribute_types[ann]
            if value_id == "self":
                class_node = find_node_by_type(ast.ClassDef, node.scopes)
                attr_node = getattr(class_node.scopes.find(node.attr), "target_node", None) \
                    if hasattr(class_node, "scopes") else None
                if ann := getattr(attr_node, "annotation", None):
                    node.annotation = ann
                elif hasattr(attr_node, "assigned_from"):
                    ann = None
                    assigned_from = attr_node.assigned_from
                    if isinstance(assigned_from, ast.Assign) and \
                            (ann := getattr(assigned_from.targets[0], "annotation", None)):
                        node.annotation = ann
                    elif isinstance(assigned_from, ast.AnnAssign):
                        node.annotation = assigned_from.annotation
            elif value_id is not None and hasattr(node, "scopes"):
                if is_enum(value_id, node.scopes):
                    node.annotation = node.scopes.find(value_id)
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        fname = get_id(node.func)
        if fname:
            # Handle methods calls by looking up the method name
            # without the prefix
            fn = node.scopes.find(fname)

            if isinstance(fn, ast.ClassDef):
                self._annotate(node, fn.name)
            elif isinstance(fn, ast.FunctionDef):
                return_type = (
                    fn.returns if hasattr(fn, "returns") and fn.returns else None
                )
                if return_type is not None:
                    node.annotation = return_type
                    lifetime = getattr(fn.returns, "lifetime", None)
                    if lifetime is not None:
                        node.annotation.lifetime = lifetime
            elif fname in self.TYPE_DICT.values() or \
                    fname in self.CONTAINER_TYPE_DICT.values():
                node.annotation = ast.Name(id=fname)

            if (func := self._clike._func_for_lookup(fname)) \
                    in self.FUNC_TYPE_MAP:
                ann = self.FUNC_TYPE_MAP[func](self, node, node.args, node.keywords)
                if ann:
                    self._annotate(node, ann)
            else:
                # Use annotation
                parse_ann = lambda x: x.value if isinstance(x, ast.Subscript) else x
                if isinstance(node.func, ast.Attribute):
                    ann = parse_ann(getattr(node.func.value, "annotation", None))
                    func_name = f"{unparse(ann)}.{node.func.attr}" \
                        if ann else None
                else:
                    ann = parse_ann(getattr(node.func, "annotation", None))
                    func_name = unparse(ann) if ann else None
                # Try to match to table entries
                if (func := self._clike._func_for_lookup(func_name)) \
                        in self.FUNC_TYPE_MAP:
                    ann = self.FUNC_TYPE_MAP[func](self, node, node.args, node.keywords)
                    if ann:
                        self._annotate(node, ann)
        return node

    def visit_Subscript(self, node: ast.Subscript):
        self.generic_visit(node)
        definition = node.value
        if hasattr(definition, "annotation"):
            self._clike._typename_from_annotation(definition)
            if hasattr(definition, "container_type") and \
                    not isinstance(node.slice, ast.Slice):
                container_type, element_type = definition.container_type
                if container_type[0] == "Dict" or isinstance(element_type, list):
                    element_type = element_type[1]
                self._annotate(node, element_type)
                node.container_type = definition.container_type
                if hasattr(definition.annotation, "lifetime"):
                    node.annotation.lifetime = definition.annotation.lifetime
            else:
                node.annotation = definition.annotation
        return node

    def visit_For(self, node: ast.For):
        self.visit(node.target)
        self.visit(node.iter)
        if hasattr(node.iter, "annotation"):
            if isinstance(node.iter.annotation, ast.Subscript):
                typ = self._clike._slice_value(node.iter.annotation)
                if isinstance(node.target, ast.Name):
                    node.target.annotation = typ
                elif isinstance(node.target, ast.Tuple) and \
                        isinstance(typ, ast.Subscript):
                    typ = self._clike._slice_value(typ)
                    if isinstance(typ, ast.Tuple):
                        for e, ann in zip(node.target.elts, typ.elts):
                            e.annotation = ann
                    else:
                        for e in node.target.elts:
                            e.annotation = typ
            elif isinstance(node.iter.annotation, ast.Tuple) and \
                    isinstance(node.target, ast.Tuple):
                for elt, ann in zip(node.target.elts, node.iter.annotation.elts):
                    if isinstance(ann, ast.Subscript) and \
                            re.match(r"list|List|tuple|Tuple", get_id(ann.value)):
                        elt.annotation = ann.slice
                    else:
                        elt.annotation = ann
            elif isinstance(node.iter, ast.Call) and \
                    get_id(node.iter.func) == "range" and \
                    isinstance(node.target, ast.Name):
                self._annotate(node.target, "int")
        self.generic_visit(node)
        return node

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> Any:
        self.generic_visit(node)
        ann_map = {}
        anns = set()
        for c in node.generators:
            if isinstance(c.iter, ast.Name):
                iter_id = get_id(c.iter)
                ann = getattr(node.scopes.find(iter_id), "annotation", None)
                if ann:
                    if isinstance(ann, ast.Subscript):
                        ann_map[get_id(c.target)] = ann.slice
                        c.target.annotation = ann
                    anns.add(get_id(ann))
        if isinstance(node.elt, ast.BinOp):
            left = node.elt.left
            right = node.elt.right
            if (id := get_id(left)) in ann_map:
                node.elt.left.annotation = ann_map[id]
            if (id := get_id(right)) in ann_map:
                node.elt.right.annotation = ann_map[id]

        if len(anns) == 1:
            self._annotate(node, f"generator[{anns.pop()}]")

        return node

    def visit_ListComp(self, node: ast.ListComp):
        self._generic_generator_visit(node)
        return node

    # def visit_DictComp(self, node: ast.DictComp) -> Any:
    #     gen_types = set()
    #     for g in node.generators:
    #         if isinstance(g.iter, ast.Name):
    #             ann = getattr(node.scopes.find(get_id(g.iter)), "annotation", None)
    #             gen_types.add(get_id(ann))

    #     if len(gen_types) == 1:
    #         self._annotate(node, f"Dict[{gen_types.pop()}]")
    #     else:
    #         self._annotate(node, "Dict")
    #     self.generic_visit(node)
    #     return node

    def visit_DictComp(self, node: ast.DictComp):
        self._generic_generator_visit(node)
        return node

    def _generic_generator_visit(self, node):
        self._block_annotations = {}
        gen_types: Set[str] = set()

        attr = None
        if isinstance(node, (ast.ListComp, ast.DictComp)):
            attr = getattr(node, "elt", None)
        else:
            attr = getattr(node, "key", None)

        for gen in node.generators:
            gen_iter = self.visit(gen.iter)
            if (ann := getattr(gen_iter, "annotation", None)):
                comp_ann = ann.slice if isinstance(ann, ast.Subscript) else ann
                if isinstance(gen.target, ast.Name):
                    self._block_annotations[get_id(gen.target)] = comp_ann
                if isinstance(attr, ast.Name):
                    gen_types.add(unparse(ann))
        if len(gen_types) == 1 and not hasattr(node, "annotation"):
            self._annotate(node, gen_types.pop())
        self.generic_visit(node)
        self._block_annotations = {}

    def visit_If(self, node: ast.If) -> Any:
        # Cover Optional types
        if isinstance(node.test, ast.Name):
            # If body has the Optional's type, as None is falsy
            ann = get_inferred_type(node.test)
            self._visit_val_branch(node, ann, get_id(node.test))
        elif isinstance(node.test, ast.UnaryOp) and \
                isinstance(node.test.op, ast.Not):
            # If body value has None type, as None is falsy
            ann = get_inferred_type(node.test.operand)
            self._visit_none_branch(node, ann, get_id(node.test.operand))
        elif isinstance(node.test, ast.BinOp) and \
                isinstance(node.test.right, ast.Constant) and \
                node.test.right.value is None:
            # Cover comparison with "None" value 
            ann = get_inferred_type(node.test.left)
            if isinstance(node.test.op, ast.IsNot) or \
                    isinstance(node.test.op, ast.NotEq):
                self._visit_val_branch(node, ann, get_id(node.test.left))
            elif isinstance(node.test.op, ast.Is) or \
                    isinstance(node.test.op, ast.Eq):
                self._visit_none_branch(node, ann, get_id(node.test.left))
        elif isinstance(node.test, ast.BoolOp):
            prev_block_annotations = self._block_annotations
            if isinstance(node.test.op, ast.And):
                for val in node.test.values:
                    if isinstance(val, ast.Call) and \
                            get_id(val.func) == "isinstance":
                        if id := get_id(val.args[0]):
                            self._block_annotations[id] = val.args[1]
            self.generic_visit(node)
            self._block_annotations = prev_block_annotations
        else:
            self.generic_visit(node)
        return node

    def _visit_val_branch(self, node: ast.If, ann, ann_node_id):
        if self._is_optional(ann):
            self.visit(node.test)
            ann_node = node.scopes.find(ann_node_id)
            ann_node.annotation = ann.slice
            for n in node.body:
                self.visit(n)
            ann_node.annotation = ast.Name(id="None")
            for n in node.orelse:
                self.visit(n)
        else:
            node.test.annotation = ann
            for n in node.body:
                self.visit(n)
            for n in node.orelse:
                self.visit(n)

    def _visit_none_branch(self, node: ast.If, ann, ann_node_id):
        if self._is_optional(ann):
            self.visit(node.test)
            ann_node = node.scopes.find(ann_node_id)
            ann_node.annotation = ast.Name(id="None")
            for n in node.body:
                self.visit(n)
            ann_node.annotation = ann.slice
            for n in node.orelse:
                self.visit(n)
        else:
            node.test.annotation = ann
            for n in node.body:
                self.visit(n)
            for n in node.orelse:
                self.visit(n)

    def _is_optional(self, annotation):
        is_optional = lambda x: get_id(x) == "Optional"
        return isinstance(annotation, ast.Subscript) and \
                is_optional(annotation.value)

    def visit_Yield(self, node: ast.Yield) -> Any:
        self.generic_visit(node)
        self._has_generators = True
        return node

    def visit_YieldFrom(self, node: ast.YieldFrom) -> Any:
        self.generic_visit(node)
        self._has_generators = True
        return node

    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> Any:
        if getattr(node, "name", None) and \
                isinstance(node.type, ast.Name):
            self._block_annotations[node.name] = ast.Name(id=get_id(node.type))
            self.generic_visit(node)
            self._block_annotations.clear()
        return node

    def visit_With(self, node: ast.With) -> Any:
        prev_block_anns = self._block_annotations
        for it in node.items:
            self.visit(it)
            if it.optional_vars and \
                    (opt_id := get_id(it.optional_vars)) and \
                    (ann := getattr(it.context_expr, "annotation", None)):
                self._block_annotations[opt_id] = ann
        for n in node.body:
            self.visit(n)
        self._block_annotations = prev_block_anns
        return node
