import ast
from py2many.analysis import get_id


class DeclarationExtractor(ast.NodeVisitor):
    def __init__(self, transpiler):
        self.transpiler = transpiler
        self.already_annotated = {}
        self.class_assignments = {}
        self.typed_vars = {}
        self._type_map = {}

    # See rust for a concrete implementation
    def type_by_initialization(self, init_str):
        return None

    def get_declarations(self):
        typed_members = self.already_annotated
        for member, var in self.class_assignments.items():
            if member in self.already_annotated:
                continue

            if var in self.typed_vars:
                typed_members[member] = self.typed_vars[var]

        for member, value in self.class_assignments.items():
            if member not in typed_members:
                typed_members[member] = self.type_by_initialization(value)

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
                if names[i] not in self.typed_vars:
                    self.typed_vars[names[i]] = typename

        for n in node.body:
            self.visit(n)

    def visit_AnnAssign(self, node, dataclass=False):
        target = node.target
        if self.is_member(target):
            type_str = self.transpiler.visit(node.annotation)
            if target.attr not in self.already_annotated:
                self.already_annotated[target.attr] = type_str
        if dataclass:
            type_str = self.transpiler.visit(node.annotation)
            if type_str in self._type_map:
                type_str = self._type_map[type_str]
            if target.id not in self.already_annotated:
                self.already_annotated[target.id] = type_str

    def visit_Assign(self, node):
        target = node.targets[0]
        if self.is_member(target):
            if target.attr not in self.class_assignments:
                self.class_assignments[target.attr] = node.value
        else:
            target = get_id(target)
            if target not in self.class_assignments:
                self.class_assignments[target] = node.value

    def is_member(self, node):
        if hasattr(node, "value"):
            if self.transpiler.visit(node.value) == "self":
                return True
        return False
