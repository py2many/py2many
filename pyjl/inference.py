import ast
from ctypes import c_int64

from py2many.inference import InferTypesTransformer, get_inferred_type, is_compatible
from py2many.analysis import get_id
from py2many.exceptions import AstIncompatibleAssign, AstUnrecognisedBinOp
from py2many.tracer import find_node_by_name, find_closest_scope_name
from pyjl.plugins import INTEGER_TYPES, NUM_TYPES
from pyjl.clike import CLikeTranspiler, class_for_typename

#########################################################

def infer_julia_types(node, extension=False):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)

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
        self._variable_types = {}
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
            get_id(node.value.annotation) if hasattr(node.value, "annotation") else None
        )

        if new_type_str is None:
            return node
        for scope in node.scopes:
            type_str = None
            if isinstance(scope, ast.FunctionDef):
                type_str = get_id(scope.returns)
                if type_str is not None:
                    if isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Mult) :
                        # specific case of ast.Mult with an int and a string
                        left_jl_annotation = node.value.left.julia_annotation if hasattr(node.value.left, "julia_annotation") else None
                        right_jl_annotation = node.value.right.julia_annotation if hasattr(node.value.right, "julia_annotation") else None
                        if(((isinstance(node.value.left, ast.Num) or left_jl_annotation in NUM_TYPES) 
                                and right_jl_annotation == "String") 
                                or ((isinstance(node.value.right, ast.Num) or right_jl_annotation in NUM_TYPES) 
                                and left_jl_annotation == "String") and isinstance(node.value.op, ast.Mult)):
                            type_str = "str"
                    elif new_type_str != type_str:
                        type_str = f"Union{'{'}{self._clike._map_type(type_str)},{self._clike._map_type(new_type_str)}{'}'}"

                    # Add julia_annotation value
                    scope.julia_annotation = self._clike._map_type(type_str)
                    setattr(scope.returns, "id", type_str)
                else:
                    # Do not overwrite source annotation with inferred
                    if scope.returns is None:
                        scope.returns = ast.Name(id=new_type_str)
                        lifetime = getattr(node.value.annotation, "lifetime", None)
                        if lifetime is not None:
                            scope.returns.lifetime = lifetime

        # print(ast.dump(node.scopes[1], indent=4))
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
                self._add_julia_type(node, annotation, target)
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
        # annotation = self._get_inferred_julia_type(self._clike._map_type(get_id(node.annotation))) # Does not appear to work
        self._add_julia_type(node, annotation, target)

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
            self._add_julia_annotation(node, get_id(left), get_id(right))
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
            self._add_julia_annotation(node, ret, ret)
            return node

        if left_id == right_id:
            # Cover division with ints
            left_annotation = (node.left.julia_annotation 
                if hasattr(node.left, "julia_annotation") else self._clike._map_type(left_id))
            right_annotation = (node.right.julia_annotation 
                if hasattr(node.right, "julia_annotation") else self._clike._map_type(right_id))
            if ((isinstance(node.left, ast.Num) or left_annotation in NUM_TYPES) and 
                    (isinstance(node.right, ast.Num) or right_annotation in NUM_TYPES)) :
                if (not isinstance(node.op, ast.Div) or 
                        getattr(node, "use_integer_div", False)):
                    node.annotation = ast.Name(id=left_id)
                    self._add_julia_annotation(node, left_id, left_id)
                else:
                    node.annotation = ast.Name(id="float")
                    self._add_julia_annotation(node, "float", "float")
                return node
            # By default, assign left
            node.annotation = left
        else:
            if ((left in INTEGER_TYPES and right == "float") or 
                    (right in INTEGER_TYPES and left == "float")):
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
                        (isinstance(node.right, ast.Str) and isinstance(node.left, ast.Num))):
                    node.annotation = ast.Name(id="str")
                if ((isinstance(node.left, ast.BoolOp) and isinstance(node.right, ast.Num)) or
                        (isinstance(node.right, ast.BoolOp) and isinstance(node.left, ast.Num))):
                    node.annotation = ast.Name(id="int")

        mapped_left = self._clike._map_type(left_id)
        mapped_right = self._clike._map_type(right_id)
        if (((mapped_left in NUM_TYPES and mapped_right == "String") 
            or (mapped_right in NUM_TYPES and mapped_left == "String")) 
            and node.op == ast.Mult):
            node.annotation = ast.Name(id="str")

        # By default (if no translation possible), the types are left_id and right_id respectively
        self._add_julia_annotation(node, left_id, right_id)

        # DEBUG
        # print(node.left.julia_annotation)
        # print(node.right.julia_annotation)

        ILLEGAL_COMBINATIONS = {}

        if left_id is not None and right_id is not None and (left_id, right_id, type(node.op)) in ILLEGAL_COMBINATIONS:
            raise AstUnrecognisedBinOp(left_id, right_id, node)
        return node

    ######################################################
    ################# Inference Methods ##################
    ######################################################

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
        ret = self._clike._map_type(get_id(python_type))
        node.julia_annotation = ret
        return ret

    def _add_julia_annotation(self, node, *defaults) :
        if isinstance(node, ast.BinOp):
            # Get default values
            left_default = defaults[0]
            right_default = defaults[1]

            # DEBUG
            # print(self._clike._map_type(left_default))
            # print(self._clike._map_type(right_default))
            
            # DEBUG
            # print(ast.dump(node))
            # if(get_id(node.right)) is not None:
            #     print("ID_RIGHT: " + get_id(node.right))
            # if(get_id(node.left)) is not None:
            #     print("ID_LEFT: " + get_id(node.left) + "\n")

            # Basic solution: Finds closest scope for assignment variable 
            # TODO: Further optimization needed
            right_scope_name = find_node_by_name(get_id(node.right), node.scopes)
            left_scope_name = find_node_by_name(get_id(node.left), node.scopes)

            # DEBUG
            # print("\nRIGHT_SCOPE_NAME: " + (right_scope_name if right_scope_name is not None else "NONE"))
            # print("LEFT_SCOPE_NAME: " + (left_scope_name if left_scope_name is not None else "NONE"))
            # print("-------FIN-------\n")

            key_right = (get_id(node.right), right_scope_name)
            key_left = (get_id(node.left), left_scope_name)

            # Assign left and right annotations
            node.left.julia_annotation = (self._variable_types[key_left] 
                if key_left in self._variable_types 
                else self._clike._map_type(left_default)
            )
            node.right.julia_annotation = (self._variable_types[key_right] 
                if key_right in self._variable_types 
                else self._clike._map_type(right_default)
            )

    def _add_julia_type(self, node, annotation, target):
        julia_annotation = self._get_inferred_julia_type(node)
        type = (self._clike._map_type(get_id(annotation)) 
            if julia_annotation == None 
            else julia_annotation
        )
        self._add_julia_variable_type(node, target, type)

    def _add_julia_variable_type(self, node, target, annotation):
        # if target (a.k.a node name) is not mapped, map it with corresponding value type
        scope = find_closest_scope_name(node.scopes)
        target_id = get_id(target)
        key = (target_id, scope)
        if(key in self._variable_types and self._variable_types[key] != annotation):
            raise AstIncompatibleAssign(f"{annotation} incompatible with {self._variable_types[key]}", node)
        self._variable_types[key] = self._clike._map_type(annotation)

