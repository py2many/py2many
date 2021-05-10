import ast

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64
from dataclasses import dataclass
from typing import Optional

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler
from py2many.tracer import is_enum


@dataclass
class InferMeta:
    has_fixed_width_ints: bool


def infer_types(node) -> InferMeta:
    visitor = InferTypesTransformer()
    visitor.visit(node)
    return InferMeta(visitor.has_fixed_width_ints)


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


class InferTypesTransformer(ast.NodeTransformer):
    """
    Tries to infer types
    """

    TYPE_DICT = {int: "int", float: "float", str: "str", bool: "bool"}
    FIXED_WIDTH_INTS = {
        bool,
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
        "bool",
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
        # TODO: remove this and make the methods into classmethods
        self._clike = CLikeTranspiler()

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
        type_annotation = ast.parse(typename).body[0].value
        node.annotation = type_annotation

    def visit_List(self, node):
        self.generic_visit(node)
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            if getattr(node, "is_annotation", False):
                return node
            else:
                elt_types = set([get_id(get_inferred_type(e)) for e in elements])
                if len(elt_types) == 1 and hasattr(elements[0], "annotation"):
                    elt_type = get_id(elements[0].annotation)
                    self._annotate(node, f"List[{elt_type}]")
        else:
            if not hasattr(node, "annotation"):
                node.annotation = ast.Name(id="List")
        return node

    def visit_Set(self, node):
        self.generic_visit(node)
        if len(node.elts) > 0:
            elements = [self.visit(e) for e in node.elts]
            elt_types = set([get_id(get_inferred_type(e)) for e in elements])
            if len(elt_types) == 1:
                elt_type = get_id(elements[0].annotation)
                self._annotate(node, f"Set[{elt_type}]")
        else:
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
            if len(key_types) == 1:
                key_type = only_key_type
            else:
                key_type = "Any"
            value_types = set([typename(e) for e in node.values])
            only_value_type = next(iter(value_types))
            if len(value_types) == 1:
                value_type = only_value_type
            else:
                value_type = "Any"
            self._annotate(node, f"Dict[{key_type}, {value_type}]")
        else:
            if not hasattr(node, "annotation"):
                node.annotation = ast.Name(id="Dict")
        return node

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)

        target = node.targets[0]
        annotation = get_inferred_type(node.value)
        if annotation is not None:
            target.annotation = annotation

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
        annotation = get_inferred_type(target)
        if hasattr(node.value, "annotation") and not annotation:
            target.annotation = node.value.annotation
        else:
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
        left_idx = (
            self.FIXED_WIDTH_INTS_NAME_LIST.index(left_id)
            if left_id in self.FIXED_WIDTH_INTS_NAME
            else -1
        )
        right_idx = (
            self.FIXED_WIDTH_INTS_NAME_LIST.index(right_id)
            if right_id in self.FIXED_WIDTH_INTS_NAME
            else -1
        )
        max_idx = max(left_idx, right_idx)
        cint64_idx = self.FIXED_WIDTH_INTS_NAME_LIST.index("c_int64")
        if widening_op:
            if max_idx not in {
                -1,
                cint64_idx,
                len(self.FIXED_WIDTH_INTS_NAME_LIST) - 1,
            }:
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
                # TODO: This is not true for dart when using integer division
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

    def visit_ClassDef(self, node):
        node.annotation = ast.Name(id=node.name)
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
            fn = node.scopes.find(fname)
            if isinstance(fn, ast.ClassDef):
                node.annotation = fn
            elif isinstance(fn, ast.FunctionDef):
                return_type = (
                    fn.returns if hasattr(fn, "returns") and fn.returns else None
                )
                if return_type is not None:
                    node.annotation = return_type
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
            self._clike._typename_from_annotation(definition)
            if hasattr(definition, "container_type"):
                _, element_type = definition.container_type
                node.annotation = ast.Name(id=element_type)
        self.generic_visit(node)
        return node
