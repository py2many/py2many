import ast
from ctypes import c_int64

from py2many.inference import InferTypesTransformer
from py2many.analysis import get_id
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.clike import class_for_typename
from pyjl.clike import CLikeTranspiler
from pyjl.helpers import get_ann_repr
from pyjl.global_vars import NONE_TYPE
from pyjl.global_vars import DEFAULT_TYPE

def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)

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
        # Holds python_type with id as variable name
        self._stack_var_map = {}
        self._none_type = NONE_TYPE
        self._default_type = DEFAULT_TYPE
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


    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)
        self.visit(node.value)

        ann = getattr(node.value, "annotation", None)
        annotation = ann if ann else getattr(node, "annotation", None)

        if annotation is None:
            # Attempt to get type
            if isinstance(node.value, ast.Call):
                typename = self._clike._generic_typename_from_annotation(node.value)
                if typename:
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
                self._verify_annotation(node, annotation, target)

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
        self._verify_annotation(node, node.annotation, node.target, inferred=False)
        return node

    def visit_BinOp(self, node):
        self.generic_visit(node)

        # Detect nesting in binary operations
        if isinstance(node.left, ast.BinOp):
            node.left.isnested = True
        if isinstance(node.right, ast.BinOp):
            node.right.isnested = True

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

        left_id = get_id(left.value) if isinstance(left, ast.Subscript) else get_id(left)
        right_id = get_id(right.value) if isinstance(right, ast.Subscript) else get_id(right)

        is_numeric = (lambda x: x == "int" or "float" or "complex"
            or x.startswith("c_int") or x.startswith("c_uint"))

        # If one or more nodes are None, skip other conditions
        if ((left is None and right is not None) 
                or (right is None and left is not None)
                or (right is None and left is None)):
            node.annotation = ast.Name(id="Any")
            self._assign_annotation(node, left, right)
            return node

        if (left_id in self.FIXED_WIDTH_INTS_NAME
                and right_id in self.FIXED_WIDTH_INTS_NAME):
            ret = self._handle_overflow(node.op, left_id, right_id)
            node.annotation = ast.Name(id=ret)
            self._assign_annotation(node, ret, ret)
            return node

        if left_id == right_id:
            # Cover division with ints
            if ((isinstance(node.left, ast.Num) or is_numeric(left_id)) and 
                    (isinstance(node.right, ast.Num) or is_numeric(right_id))):
                if (not isinstance(node.op, ast.Div) or 
                        getattr(node, "use_integer_div", False)):
                    node.annotation = left
                    self._assign_annotation(node, left, left)
                else:
                    node.annotation = ast.Name(id="float")
                    self._assign_annotation(node, node.annotation, node.annotation)
                return node

            # By default, assign left
            node.annotation = left
        else:
            if ((left_id == "int" and right_id == "float") or 
                    (right_id == "int" and left == "float")):
                node.annotation = ast.Name(id="float")
                self._assign_annotation(node, node.annotation, node.annotation)
                return node
            if (left_id, right_id) in { 
                ("int", "complex"),
                ("complex", "int"),
                ("float", "complex"),
                ("complex", "float"),
            }:
                node.annotation = ast.Name(id="complex")
                self._assign_annotation(node, node.annotation, node.annotation)
                return node

        # By default (if no translation possible), the types are left_id and right_id respectively
        self._assign_annotation(node, left, right)

        ILLEGAL_COMBINATIONS = {}

        if left_id is not None and right_id is not None and (left_id, right_id, type(node.op)) in ILLEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)
        return node


    ######################################################
    ################# Inference Methods ##################
    ######################################################

    def _verify_annotation(self, node, annotation, target, inferred = True):
        annotation.is_inferred = inferred
        var_name = get_id(target)
        ann_str = get_ann_repr(annotation)
        map_ann = node.scopes.find(var_name)
        map_ann_str = get_ann_repr(map_ann)
        if(map_ann_str and getattr(map_ann, "is_inferred", True) == False and ann_str != self._default_type \
                and map_ann_str != self._default_type and ann_str != map_ann_str):
            raise AstIncompatibleAssign(
                f"Variable {var_name}: {ann_str} incompatible with {map_ann_str}", 
                node
            )

    def _assign_annotation(self, node, *defaults):
        if isinstance(node, ast.BinOp):
            # Get default values
            left_default = defaults[0]
            right_default = defaults[1]

            left_ann = node.scopes.find(get_id(node.left))
            right_ann = node.scopes.find(get_id(node.right)) \

            # Assign left and right annotations
            node.left.annotation = (left_ann
                if left_ann else left_default
            )
            node.right.annotation = (right_ann
                if right_ann else right_default
            )

