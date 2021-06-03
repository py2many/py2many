import ast
from py2many.analysis import get_id
from typing import Any, Dict, Tuple


class DeclarationExtractor(ast.NodeVisitor):
    def __init__(self, transpiler):
        self.transpiler = transpiler
        # maps name -> (type, default_value)
        self.annotated_members: Dict[str, Tuple[str, Any]] = {}
        self.class_assignments = {}
        self.member_assignments = {}
        self.typed_function_args = {}

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
                    None,
                )

        return typed_members

    def visit_ClassDef(self, node: ast.ClassDef):
        decorators = [d.id for d in node.decorator_list]
        if len(node.decorator_list) > 0 and "dataclass" in decorators:
            node.is_dataclass = True
            dataclass_members = []
            node.dataclass_fields = []
            for child in node.body:
                if isinstance(child, ast.AnnAssign):
                    dataclass_field = self.visit_AnnAssign(child, dataclass=True)
                    dataclass_members.append(child)
                    node.dataclass_fields.append(dataclass_field)
            for m in dataclass_members:
                node.body.remove(m)
        else:
            node.is_dataclass = False
            self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):
        types, names = self.transpiler.visit(node.args)

        for i in range(len(names)):
            typename = types[i]
            if typename and typename != "T":
                if names[i] not in self.typed_function_args:
                    self.typed_function_args[names[i]] = typename

        self.generic_visit(node)

    def visit_AnnAssign(self, node, dataclass=False):
        target = node.target
        if self.is_member(target):
            type_str = self.transpiler._typename_from_annotation(node)
            if target.attr not in self.annotated_members:
                self.annotated_members[target.attr] = (type_str, node.value)
        if dataclass:
            type_str = self.transpiler._typename_from_annotation(node)
            if target.id not in self.annotated_members:
                self.annotated_members[target.id] = (type_str, node.value)

    def visit_Assign(self, node):
        target = node.targets[0]
        if self.is_member(target):
            if target.attr not in self.member_assignments:
                self.member_assignments[target.attr] = node.value
        else:
            target = get_id(target)
            if target not in self.class_assignments:
                self.class_assignments[target] = node.value

    def is_member(self, node):
        if hasattr(node, "value"):
            if self.transpiler.visit(node.value) == "self":
                return True
        return False
