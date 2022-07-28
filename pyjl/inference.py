import ast
from py2many.external_modules import ExternalBase
from py2many.helpers import get_ann_repr

from py2many.inference import InferMeta, InferTypesTransformer
from py2many.analysis import get_id
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from pyjl.global_vars import DEFAULT_TYPE, SEP

def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)
    return InferMeta(visitor.has_fixed_width_ints)

class InferJuliaTypesTransformer(InferTypesTransformer, ExternalBase):
    """
    Implements Julia type inference logic
    """

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_LIST
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def __init__(self):
        super().__init__()
        self._default_type = DEFAULT_TYPE
        self._func_type_map = self.FUNC_TYPE_MAP
        # Get external module features
        self.import_external_modules("Julia")

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        # Get annotation
        super().visit_Assign(node)

        for target in node.targets:
            target_has_annotation = hasattr(target, "annotation")
            inferred = (
                getattr(target.annotation, "inferred", False)
                if target_has_annotation
                else False
            )
            # target_annotation = getattr(target, "annotation", None)
            # target_typename = self._clike._generic_typename_from_type_node(target_annotation)
            # value_typename = self._clike._generic_typename_from_type_node(annotation)
            # target_class = class_for_typename(target_typename, None)
            # value_class = class_for_typename(value_typename, None)
            # compatible = is_compatible(target_class, value_class)
            ###############
            # TODO: We need to improve is_compatible to support a broader analysis
            # For now, _verify_annotation performs a string-based comparison as a fallback
            if hasattr(node, "annotation"):
                self._verify_annotation(node, getattr(target, "annotation", None), 
                    target, inferred=inferred)
        return node

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        super().visit_AnnAssign(node)
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

        # If one node is None, skip other conditions
        if left is None or right is None:
            return node

        left_id = get_id(left.value) if isinstance(left, ast.Subscript) else get_id(left)
        right_id = get_id(right.value) if isinstance(right, ast.Subscript) else get_id(right)

        is_numeric = (lambda x: x == "int" or "float" or "complex"
            or (isinstance(x, str) and 
                (x.startswith("c_int") or x.startswith("c_uint"))))

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
            # promotion
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

        # By default (if no translation possible), the types are left_id and right_id respectively
        self._assign_annotation(node, left, right)

        # Changed legal for illegal combinations
        ILLEGAL_COMBINATIONS = {}

        if left_id is not None and right_id is not None and (left_id, right_id, type(node.op)) in ILLEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)
        return node

    ######################################################
    ################# Inference Methods ##################
    ######################################################

    def _verify_annotation(self, node, annotation, target, inferred = False):
        annotation.is_inferred = inferred
        ann_str = get_ann_repr(annotation, sep=SEP)
        # Find another variable
        var_name = get_id(target)
        map_ann = getattr(node.scopes.find(var_name), "annotation", None)
        map_ann_str = get_ann_repr(map_ann, sep=SEP) if map_ann else None
        if(map_ann_str and not getattr(map_ann, "is_inferred", True) and ann_str != self._default_type \
                and map_ann_str != self._default_type and ann_str.lower() != map_ann_str.lower()):
            raise AstIncompatibleAssign(
                f"Variable {var_name}: {ann_str} incompatible with {map_ann_str}", 
                node
            )

    def _assign_annotation(self, node, *defaults):
        if isinstance(node, ast.BinOp):
            # Get default values
            left_default = defaults[0]
            right_default = defaults[1]

            left_ann = None
            right_ann = None
            if get_id(node.left):
                left_ann = getattr(node.scopes.find(get_id(node.left)),
                    "annotation", None)
            if get_id(node.right):
                right_ann = getattr(node.scopes.find(get_id(node.right)),
                    "annotation", None)

            # Assign left and right annotations
            node.left.annotation = (left_ann
                if left_ann else left_default
            )
            node.right.annotation = (right_ann
                if right_ann else right_default
            )

