import ast
from ctypes import c_int64

import inspect
from typing import Any

from py2many.inference import InferTypesTransformer, get_inferred_type, is_compatible
from py2many.analysis import get_id
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.tracer import find_node_by_type
from py2many.clike import class_for_typename
from pyjl.clike import _NONE_TYPE, CLikeTranspiler
from pyjl.global_vars import CHANNELS, RESUMABLE
from pyjl.helpers import find_assign_value, get_str_repr

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
        # Holds Tuple(julia_type, python_type) with id as variable name
        self._stack_var_map = {}
        self._none_type = _NONE_TYPE
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


    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self._generic_scope_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._generic_scope_visit(node)
        # if get_id(node.returns) == "Generator":
        #     if RESUMABLE in node.parsed_decorators:
        #         node.returns = None
        #     elif CHANNELS in node.parsed_decorators or \
        #             getattr(node, "returns_channel", None):
        #         node.returns = ast.Name(id="Channel")
        #         print(ast.dump(node.returns))
        return node

    def visit_Return(self, node: ast.Return):
        self.generic_visit(node)
        new_type_str = (
            get_id(node.value.annotation) if hasattr(node.value, "annotation") else None
        )

        func_node = find_node_by_type(ast.FunctionDef, node.scopes)
        type_str = get_id(func_node.returns) if func_node else None
        if new_type_str is None:
            return node
        
        # Setting type_str to infered type
        if type_str is not None:
            type_str = new_type_str
            # Add julia_annotation value
            func_node.julia_annotation = get_str_repr(type_str, self._clike._map_type, self._none_type)
            setattr(func_node.returns, "id", type_str)
        else:
            # Do not overwrite source annotation with inferred
            if func_node.returns is None:
                func_node.returns = ast.Name(id=new_type_str)
                lifetime = getattr(node.value.annotation, "lifetime", None)
                if lifetime is not None:
                    func_node.returns.lifetime = lifetime
        return node

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)
        self.visit(node.value)

        ann = getattr(node.value, "annotation", None)
        annotation = ann if ann else getattr(node, "annotation", None)

        if annotation is None:
            # Attempt to get type
            if isinstance(node.value, ast.Call):
                node_id = get_id(node.value.func)
                try:
                    id_type = self._clike._generic_typename_from_type_node(node_id)
                    if id_type is not Any and id_type is not None and inspect.isclass(id_type):
                        annotation = ast.Name(id=node_id)
                    else:
                        return node
                except Exception:
                    return node
            elif isinstance(node.value, ast.Name):
                # Try to get related assignment
                assign_ann = self._find_annotated_assign(node.value, node.scopes)
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
                self._add_annotation(node, annotation, target)

        # TODO: Call is_compatible to check if the inferred and user provided annotations conflict
        return node

    def _find_annotated_assign(self, node, scopes):
        assign = find_assign_value(get_id(node), scopes)
        if assign:
            if (assign_ann := getattr(assign, "annotation", None)):
                return assign_ann
            else:
                return self._find_annotated_assign(assign, scopes)
        else:
            return None

    def visit_AnnAssign(self, node: ast.AnnAssign) -> ast.AST:
        self.generic_visit(node)

        ann = getattr(node.value, "annotation", None)
        target = node.target
        annotation = ann if ann else getattr(node, "annotation", None)
        node.annotation = annotation
        self._add_annotation(node, annotation, target)

        target_typename = self._clike._typename_from_annotation(target)
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

        # left_id = get_str_repr(left)
        left_id = get_id(left)
        # right_id = get_str_repr(right)
        right_id = get_id(right)

        is_numeric = (lambda x: x == "int" or "float" or "complex"
            or x.startswith("c_int") or x.startswith("c_uint"))

        # If one or more nodes are None, skip other conditions
        if ((left is None and right is not None) 
                or (right is None and left is not None)
                or (right is None and left is None)):
            self._add_julia_annotation(node, left, right)
            return node

        if (left_id in self.FIXED_WIDTH_INTS_NAME
                and right_id in self.FIXED_WIDTH_INTS_NAME):
            ret = self._handle_overflow(node.op, left_id, right_id)
            self._add_julia_annotation(node, ret, ret)
            return node

        if left_id == right_id:
            # Cover division with ints
            if ((isinstance(node.left, ast.Num) or is_numeric(left_id)) and 
                    (isinstance(node.right, ast.Num) or is_numeric(right_id))):
                if (not isinstance(node.op, ast.Div) or 
                        getattr(node, "use_integer_div", False)):
                    node.annotation = left
                    self._add_julia_annotation(node, left, left)
                else:
                    node.annotation = ast.Name(id="float")
                    self._add_julia_annotation(node, "float", "float")
                return node

            # By default, assign left
            node.annotation = left
        else:
            if ((left_id == "int" and right == "float") or 
                    (right_id == "int" and left == "float")):
                self._add_julia_annotation(node, "float", "float")
                node.annotation = ast.Name(id="float")
                return node
            if (left_id, right_id) in { 
                ("int", "complex"),
                ("complex", "int"),
                ("float", "complex"),
                ("complex", "float"),
            }:
                self._add_julia_annotation(node, "complex", "complex")
                node.annotation = ast.Name(id="complex")
                return node
            if isinstance(node.op, ast.Mult):
                if ((isinstance(node.left, ast.List) and isinstance(node.right, ast.Num)) or 
                        (isinstance(node.right, ast.List) and isinstance(node.left, ast.Num))):
                    node.annotation = ast.Name(id="List")
                if ((isinstance(node.left, ast.Str) and isinstance(node.right, ast.Num)) or 
                        (isinstance(node.right, ast.Str) and isinstance(node.left, ast.Num))
                        or (left_id == "str" and right_id == "int") or (left_id == "int" and right_id == "str")):
                    node.annotation = ast.Name(id="str")
                if ((isinstance(node.left, ast.BoolOp) and isinstance(node.right, ast.Num)) or
                        (isinstance(node.right, ast.BoolOp) and isinstance(node.left, ast.Num))):
                    node.annotation = ast.Name(id="int")

        # By default (if no translation possible), the types are left_id and right_id respectively
        self._add_julia_annotation(node, left, right)

        ILLEGAL_COMBINATIONS = {}

        if left_id is not None and right_id is not None and (left_id, right_id, type(node.op)) in ILLEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)
        return node

    def visit_withitem(self, node: ast.withitem) -> Any:
        self.generic_visit(node)
        var_value = get_str_repr(node.context_expr)

        if ann := getattr(node.context_expr, "annotation", None):
            self._add_annotation(node, ann, node.optional_vars)
        else:
            id_type = self._clike._generic_typename_from_type_node(var_value)
            if id_type != self._clike._default_type and id_type is not None:
                annotation = ast.Name(id=var_value)
                self._add_annotation(node, annotation, node.optional_vars)

        return node

    ######################################################
    ################# Inference Methods ##################
    ######################################################

    def _generic_scope_visit(self, node):
        curr_state = dict(self._stack_var_map)

        for n in node.body:
            self.visit(n)

        # Assign variables to field in function node
        node.var_map = self._stack_var_map

        # Returns to state before visiting the function body
        # This accounts for nested functions
        self._stack_var_map = curr_state

    def _get_inferred_julia_type(self, node):
        if hasattr(node, "julia_annotation"):
            return node.julia_annotation
        if isinstance(node, ast.Name):
            if not hasattr(node, "scopes"):
                return None
            definition = node.scopes.find(get_id(node))
            # Prevent infinite recursion
            if definition and definition != node:
                return self._get_inferred_julia_type(definition)
        
        python_type = get_inferred_type(node)
        ret = get_str_repr(python_type, self._clike._map_type, self._none_type)
        node.julia_annotation = ret
        return ret

    def _add_julia_annotation(self, node, *defaults) :
        if isinstance(node, ast.BinOp):
            # Get default values
            left_default = get_str_repr(defaults[0], self._clike._map_type, self._none_type)
            right_default = get_str_repr(defaults[1], self._clike._map_type, self._none_type)

            left_ann = self._stack_var_map[get_id(node.left)][0] \
                if get_id(node.left) in self._stack_var_map \
                else None
            right_ann = self._stack_var_map[get_id(node.right)][0] \
                if get_id(node.right) in self._stack_var_map \
                else None

            # Assign left and right annotations
            node.left.julia_annotation = (left_ann
                if left_ann and left_ann != self._none_type
                else left_default
            )
            node.right.julia_annotation = (right_ann
                if right_ann and right_ann != self._none_type
                else right_default
            )

    def _append_to_type_map(self, node, annotation, target):
        python_annotation = get_str_repr(annotation)
        parsed_annotation = get_str_repr(annotation, self._clike._map_type, self._none_type)
        julia_annotation = self._get_inferred_julia_type(node)
        julia_type = (parsed_annotation 
            if julia_annotation == None or julia_annotation == self._none_type
            else julia_annotation
        )

        var_name = get_str_repr(target)
        if(python_annotation and var_name in self._stack_var_map and self._stack_var_map[var_name][1] != python_annotation):
            raise AstIncompatibleAssign(f"Variable {var_name}: {python_annotation} incompatible with {self._stack_var_map[var_name][1]}", node)
        self._stack_var_map[var_name] = (julia_type, python_annotation)

    def _add_annotation(self, node, annotation, target):
        self._append_to_type_map(node, annotation, target)
        target.annotation = annotation
        target.annotation.inferred = True

