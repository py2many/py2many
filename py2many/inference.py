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
from dataclasses import dataclass
from typing import Optional, Set, cast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node
from py2many.astx import LifeTime
from py2many.clike import CLikeTranspiler, class_for_typename
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.tracer import is_enum

try:
    from typpete.context import Context
    from typpete.inference_runner import infer as infer_types_ast
    from typpete.z3_types import TypesSolver
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


def infer_types_typpete(node) -> InferMeta:
    solver = TypesSolver(node)
    context = Context(node, node.body, solver)
    for stmt in node.body:
        infer_types_ast(stmt, context, solver)

    solver.push()

    return InferMeta(True)


def get_inferred_type(node):
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node and definition is not None:
            return get_inferred_type(definition)
    elif isinstance(node, ast.Constant) or isinstance(node, ast.NameConstant):
        return InferTypesTransformer._infer_primitive(node.value)
    if hasattr(node, "annotation"):
        return node.annotation
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


class InferTypesTransformer(ast.NodeTransformer):
    """
    Tries to infer types
    """

    TYPE_DICT = {
        int: "int",
        float: "float",
        str: "str",
        bool: "bool",
        bytes: "bytes",
        complex: "complex",
        type(...): "...",
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
        return node

    def visit_Constant(self, node):
        return self.visit_NameConstant(node)

    @staticmethod
    def _annotate(node, typename: str):
        # ast.parse produces a Module object that needs to be destructured
        type_annotation = cast(ast.Expr, create_ast_node(typename, node)).value
        node.annotation = type_annotation

    def visit_List(self, node):
        self.generic_visit(node)
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            if getattr(node, "is_annotation", False):
                return node
            else:
                elt_types: Set[str] = set()
                for e in elements:
                    typ = get_inferred_type(e)
                    if typ is not None:
                        elt_types.add(ast.unparse(typ))
                if len(elt_types) == 0:
                    node.annotation = ast.Name(id="List")
                elif len(elt_types) == 1:
                    self._annotate(node, f"List[{elt_types.pop()}]")
                else:
                    self._annotate(node, f"List[Union[{', '.join(elt_types)}]]")
        else:
            if not hasattr(node, "annotation"):
                node.annotation = ast.Name(id="List")
        return node

    def visit_Set(self, node):
        self.generic_visit(node)
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            elt_types = {get_id(get_inferred_type(e)) for e in elements}
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
                return CLikeTranspiler._generic_typename_from_annotation(e)

            key_types = {typename(e) for e in node.keys}
            only_key_type = next(iter(key_types))
            if len(key_types) == 1:
                key_type = only_key_type
            else:
                key_type = "Any"
            value_types = {typename(e) for e in node.values}
            only_value_type = next(iter(value_types))
            if len(value_types) == 1:
                value_type = only_value_type
            else:
                value_type = "Any"
            self._annotate(node, f"Dict[{key_type}, {value_type}]")
            lifetimes = {
                getattr(e.annotation, "lifetime", None)
                for e in node.values
                if hasattr(e, "annotation")
            }
            only_lifetime = next(iter(lifetimes)) if len(lifetimes) == 1 else None
            if len(lifetimes) == 1 and only_lifetime != None:
                lifetime = only_lifetime
            else:
                lifetime = LifeTime.UNKNOWN
            node.annotation.lifetime = lifetime
        else:
            if not hasattr(node, "annotation"):
                node.annotation = ast.Name(id="Dict")
        return node

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)
        self.visit(node.value)

        annotation = getattr(node.value, "annotation", None)
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
                target.annotation = annotation
                target.annotation.inferred = True
        # TODO: Call is_compatible to check if the inferred and user provided annotations conflict
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        self.generic_visit(node)

        node.target.annotation = node.annotation
        target = node.target
        target_typename = CLikeTranspiler._typename_from_annotation(target)
        if target_typename in self.FIXED_WIDTH_INTS_NAME:
            self.has_fixed_width_ints = True
        annotation = get_inferred_type(node.value)
        value_typename = CLikeTranspiler._generic_typename_from_type_node(annotation)
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

        # Container multiplication
        if isinstance(node.op, ast.Mult) and {left_id, right_id} in [
            {"bytes", "int"},
            {"str", "int"},
            {"tuple", "int"},
            {"List", "int"},
        ]:
            node.annotation = ast.Name(id=left_id)
            return node

        LEGAL_COMBINATIONS = {("str", ast.Mod), ("List", ast.Add)}

        if left_id is not None and (left_id, type(node.op)) not in LEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)

        return node

    def visit_ClassDef(self, node):
        node.annotation = ast.Name(id=node.name)
        self.generic_visit(node)
        return node

    def visit_Attribute(self, node):
        value_id = get_id(node.value)
        if value_id is not None and hasattr(node, "scopes"):
            if is_enum(value_id, node.scopes):
                node.annotation = node.scopes.find(value_id)
        return node

    def visit_Call(self, node):
        fname = get_id(node.func)
        if fname is not None:
            # Handle methods calls by looking up the method name
            # without the prefix
            # TODO: use remove suffix
            if fname.startswith("self."):
                fname = fname.split(".", 1)[1]
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
            elif fname in {"max", "min"}:
                return_type = get_inferred_type(node.args[0])
                if return_type is not None:
                    node.annotation = return_type
            elif fname in self.TYPE_DICT.values():
                node.annotation = ast.Name(id=fname)
        self.generic_visit(node)
        return node

    def visit_Subscript(self, node):
        definition = node.scopes.find(get_id(node.value))
        if hasattr(definition, "annotation"):
            CLikeTranspiler._typename_from_annotation(definition)
            if hasattr(definition, "container_type"):
                container_type, element_type = definition.container_type
                if container_type == "Dict" or isinstance(element_type, list):
                    element_type = element_type[1]
                node.annotation = ast.Name(id=element_type)
                if hasattr(definition.annotation, "lifetime"):
                    node.annotation.lifetime = definition.annotation.lifetime
        self.generic_visit(node)
        return node

    def visit_For(self, node):
        self.visit(node.target)
        self.visit(node.iter)
        if hasattr(node.iter, "annotation") and isinstance(
            node.iter.annotation, ast.Subscript
        ):
            typ = CLikeTranspiler._slice_value(node.iter.annotation)

            if isinstance(node.target, ast.Name):
                node.target.annotation = typ
            elif isinstance(node.target, ast.Tuple) and isinstance(typ, ast.Subscript):
                typ = CLikeTranspiler._slice_value(typ)
                for e in node.target.elts:
                    e.annotation = typ
        self.generic_visit(node)
        return node

    def visit_BoolOp(self, node: ast.BoolOp):
        node.annotation = ast.Name(id="bool")
        return node
