import ast
from typing import Any, Dict, Tuple
from py2many.ast_helpers import get_id


class DeclarationExtractor(ast.NodeVisitor):
    def __init__(self, transpiler):
        self.transpiler = transpiler
        # maps: name -> (type, default_value)
        self.annotated_members: Dict[str, Tuple[str, Any]] = {}
        self.class_assignments = {}
        self.member_assignments = {}
        self.typed_function_args = {}

    def _maybe_rename_key(self, key):
        if key in self.transpiler._keywords:
            return key + "_"
        else:
            return key

    def get_declarations(self):
        # strip out default values for backward compat with callers
        typed_members = {k: v[0] for k, v in self.annotated_members.items()}
        for member, var in self.member_assignments.items():
            if member in self.annotated_members:
                continue

            if var in self.typed_function_args:
                typed_members[member] = self.typed_function_args[var]

        for member, value in self.member_assignments.items():
            if member not in typed_members:
                typed_members[member] = self.transpiler._typename_from_annotation(value)

        typed_members = {self._maybe_rename_key(k): v for k, v in typed_members.items()}
        return typed_members

    def get_declarations_with_defaults(self):
        typed_members = self.annotated_members
        for member, var in self.member_assignments.items():
            if member in self.annotated_members:
                continue

            if var in self.typed_function_args:
                typed_members[member] = (self.typed_function_args[var], None)

        for member, value in self.member_assignments.items():
            if member not in typed_members:
                typed_members[member] = (
                    self.transpiler._typename_from_annotation(value),
                    value,
                )

        return typed_members

    def visit_ClassDef(self, node: ast.ClassDef):
        decorators = [get_id(d) for d in node.decorator_list]
        if len(node.decorator_list) > 0 and "dataclass" in decorators:
            node.is_dataclass = True
            dataclass_members = []
            for child in node.body:
                if isinstance(child, ast.AnnAssign):
                    self.visit_AnnAssign(child, dataclass=True)
                    dataclass_members.append(child)
            for m in dataclass_members:
                node.body.remove(m)
        else:
            node.is_dataclass = False
            self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    # Get Default values here
    def visit_FunctionDef(self, node):
        self.generic_visit(node)
        types, names = self.transpiler.visit(node.args)

        for i in range(len(names)):
            typename = types[i]
            if typename and typename != "T":
                if names[i] not in self.typed_function_args:
                    self.typed_function_args[names[i]] = typename


    def visit_Call(self, node: ast.Call) -> Any:
        # Only visit arguments to avoid function 
        # calls with the syntax: self.<func_name>
        for arg in node.args:
            self.visit(arg)
        return node

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        self.generic_visit(node)
        if node.attr not in self.member_assignments and \
                get_id(node.value) == "self":
            self.member_assignments[node.attr] = None

    def visit_AnnAssign(self, node: ast.AnnAssign, dataclass=False):
        val = self._get_assign_val(node)
        parent = node.scopes[-1]
        target = node.target
        target_id = self._get_target_id(target)
        if target_id is None:
            return

        # Preserve string based types (Forward refs) instead of converting them
        # to default type
        type_str = None
        if isinstance(node.annotation, ast.Constant):
            type_str = node.annotation.value
        if type_str is None:
            type_str = self.transpiler._typename_from_annotation(node)
        if target_id not in self.annotated_members:
            self.annotated_members[target_id] = (type_str, val)

        if dataclass:
            type_str = self.transpiler._typename_from_annotation(node)
            if target_id not in self.annotated_members:
                self.annotated_members[target_id] = (type_str, val)

        if self._is_member(target) or isinstance(parent, ast.ClassDef):
            id = self._get_target_id(target)
            if id and id not in self.annotated_members:
                self.annotated_members[id] = (type_str, val)
        else:
            node.class_assignment = True
            if target_id not in self.class_assignments:
                self.class_assignments[target_id] = val


    def visit_Assign(self, node: ast.Assign):
        val = self._get_assign_val(node)   
        parent = node.scopes[-1]
        target = node.targets[0]
        if self._is_member(target) or isinstance(parent, ast.ClassDef):
            id = self._get_target_id(target)
            if id and (id not in self.member_assignments or \
                    (id in self.member_assignments and 
                        not self.member_assignments[id])):
                self.member_assignments[id] = val
        else:
            node.class_assignment = True
            target = get_id(target)
            if target is not None and target not in self.class_assignments:
                self.class_assignments[target] = val


    def _get_target_id(self, target):
        if isinstance(target, ast.Subscript):
            return self._get_target_id(target.value)
        elif isinstance(target, ast.Attribute):
            return target.attr
        else:
            return get_id(target)


    def _is_member(self, node):
        """Checks if an attribute is a class field"""
        return isinstance(node, ast.Attribute) and get_id(node.value) == "self"


    def _get_assign_val(self, node):
        """Gets the assignment value for the class fields. 
        Assignment values are only considered if assignments 
        belong to the classes body or to the __init__ method"""
        parent = node.scopes[-1]
        is_init = isinstance(parent, ast.FunctionDef) and parent.name == "__init__"
        return node.value if \
            (is_init or isinstance(parent, ast.ClassDef)) \
            else None
