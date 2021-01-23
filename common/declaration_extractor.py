import ast


class DeclarationExtractor(ast.NodeVisitor):
    def __init__(self, transpiler):
        self.transpiler = transpiler
        self.already_annotated = {}
        self.class_assignments = {}
        self.typed_vars = {}

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

    def visit_AnnAssign(self, node):
        target = node.target
        if self.is_member(target):
            type_str = self.transpiler.visit(node.annotation)
            if target.attr not in self.already_annotated:
                self.already_annotated[target.attr] = type_str

    def visit_Assign(self, node):
        target = node.targets[0]
        if self.is_member(target):
            # target = self.transpiler.visit(target)
            value = self.transpiler.visit(node.value)
            if target.attr not in self.class_assignments:
                self.class_assignments[target.attr] = value

    def is_member(self, node):
        if hasattr(node, "value"):
            if self.transpiler.visit(node.value) == "self":
                return True
        return False
