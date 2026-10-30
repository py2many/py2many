from typing import Any, Dict, Tuple

import spy_ast.ast as ast

from py2many.ast_helpers import get_id


class DeclarationExtractor(ast.NodeVisitor):
    def __init__(self, transpiler):
        self.transpiler = transpiler
        # maps name -> (type, default_value)
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
                    None,
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
            # Paren-style sealed variants: `ADD(Expr, Expr)` declares a
            # tuple variant with positional payloads. Record it as a
            # `Tuple[...]` annotation so backends share Tuple handling.
            if "sealed" in decorators:
                for child in node.body:
                    if (
                        isinstance(child, ast.Expr)
                        and isinstance(child.value, ast.Call)
                        and isinstance(child.value.func, ast.Name)
                        and not child.value.keywords
                    ):
                        variant = child.value.func.id
                        if variant.startswith("__"):
                            continue
                        arg_names = []
                        for arg in child.value.args:
                            arg_id = get_id(arg)
                            if arg_id is not None:
                                arg_names.append(arg_id)
                            elif isinstance(arg, ast.Constant) and isinstance(
                                arg.value, str
                            ):
                                arg_names.append(arg.value)
                            else:
                                # Fall back to transpiler mapping for
                                # complex payload types (e.g. Subscript).
                                try:
                                    arg_names.append(
                                        self.transpiler._typename_from_annotation(
                                            ast.AnnAssign(
                                                target=ast.Name(
                                                    id="_", ctx=ast.Store()
                                                ),
                                                annotation=arg,
                                                simple=1,
                                            )
                                        )
                                    )
                                except Exception:
                                    arg_names.append("Any")
                        tuple_typename = f"Tuple[{', '.join(arg_names)}]"
                        if variant not in self.annotated_members:
                            self.annotated_members[variant] = (
                                tuple_typename,
                                None,
                            )
                        # Mark as class-level variant for sealed handling.
                        variant_key = ast.Name(id=variant, ctx=ast.Store())
                        if variant_key not in self.class_assignments:
                            self.class_assignments[variant_key] = child.value

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
        target_id = get_id(target)
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
            self.annotated_members[target_id] = (type_str, node.value)

        if not self.is_member(target):
            node.class_assignment = True
            if target not in self.class_assignments:
                self.class_assignments[target] = node.value

        if dataclass:
            type_str = self.transpiler._typename_from_annotation(node)
            if target_id not in self.annotated_members:
                self.annotated_members[target_id] = (type_str, node.value)

    def visit_Assign(self, node):
        target = node.targets[0]
        if self.is_member(target):
            if target.attr not in self.member_assignments:
                self.member_assignments[target.attr] = node.value
        else:
            node.class_assignment = True
            target = get_id(target)
            if target not in self.class_assignments:
                self.class_assignments[target] = node.value

    def visit_With(self, node):
        for item in node.items:
            if item.optional_vars:
                target = get_id(item.optional_vars)
                if target and target not in self.class_assignments:
                    self.class_assignments[target] = item.context_expr
        self.generic_visit(node)

    def is_member(self, node):
        if hasattr(node, "value"):
            if self.transpiler.visit(node.value) == "self":
                return True
        return False
