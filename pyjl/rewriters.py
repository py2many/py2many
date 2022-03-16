from __future__ import annotations
import ast
from typing import Any, Dict
from py2many.analysis import IGNORED_MODULE_SET

from py2many.input_configuration import ParseFileStructure
from py2many.tracer import find_node_matching_type
from py2many.ast_helpers import get_id
import pyjl.juliaAst as juliaAst
from pyjl.plugins import JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE
from pyjl.transpiler import get_decorator_id


def julia_decorator_rewriter(tree, input_config, filename):
    JuliaDecoratorRewriter(input_config, filename).visit(tree)


class JuliaMethodCallRewriter(ast.NodeTransformer):
    def visit_Call(self, node):
        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]

        fname = node.func
        if isinstance(fname, ast.Attribute):
            new_func_name = fname.attr

            if get_id(fname.value):
                node0 = ast.Name(id=get_id(fname.value), lineno=node.lineno)
            else:
                node0 = fname.value

            if new_func_name == "join":
                # Join with empty string if no content is present
                if not node0:
                    node0 = f"\"\""
                args = node.args + [node0]
            else:
                args = [node0] + node.args

            node.func = ast.Name(
                id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        if isinstance(fname, ast.Name):
            if get_id(node.func) == "join" and node.args:
                args.reverse()

        node.args = args
        return node


class JuliaDecoratorRewriter(ast.NodeTransformer):
    def __init__(self, input_config: Dict, filename: str) -> None:
        super().__init__()
        self._input_config_map = (ParseFileStructure.retrieve_structure(filename, input_config)
                                  if input_config else None)

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)
        node_name = get_id(node)
        node_scope_name = None
        if self._input_config_map:
            if len(node.scopes) > 2:
                node_class = find_node_matching_type(ast.ClassDef, node.scopes)
                node_scope_name = get_id(node_class) if node_class else None

            node_field_map = ParseFileStructure.get_function_attributes(node_name,
                                                                        node_scope_name, self._input_config_map)

            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        class_name = get_id(node)
        if self._input_config_map:
            node_field_map = ParseFileStructure.get_class_attributes(
                class_name, self._input_config_map)
            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node


class JuliaClassRewriter(ast.NodeTransformer):
    """Transforms Python classes into Julia compatible nodes"""
    def __init__(self) -> None:
        super().__init__()
        self._hierarchy_map = {}
        self._import_list = []  # TODO: Consider imported classes
        self._import_count = 0
        self._ignored_module_set = IGNORED_MODULE_SET
        self._class_fields: Dict[str, Any] = {}

    def visit_Module(self, node: ast.Module) -> Any:
        node.lineno = 0
        node.col_offset = 0
        node.class_names = []

        # visit nodes recursively
        for n in node.body:
            self.visit(n)

        # Create abstract types if needed
        abstract_types = []
        l_no = self._import_count
        for (class_name, (extends_lst, is_jlClass)) in self._hierarchy_map.items():
            node.class_names.append(class_name)
            if not is_jlClass:
                # TODO: Investigate Julia traits
                nameVal = ast.Name(id=class_name)
                extends = ast.Name(id=f"Abstract{extends_lst[0]}") \
                    if extends_lst else None
                abstract_types.append(
                    juliaAst.AbstractType(value=nameVal, extends=extends,
                                          ctx=ast.Load, lineno=l_no, col_offset=0))
                # increment linenumber
                l_no += 1

        if abstract_types:
            node.body = node.body[:self._import_count] + \
                abstract_types + node.body[self._import_count:]

        # Visit Function nodes later to account for all classes
        for n in node.body:
            if isinstance(n, ast.ClassDef):
                body = []
                self._class_fields = {}
                for d in n.body:
                    if isinstance(d, ast.FunctionDef):
                        if d.name in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
                            JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE[d.name](self, d)
                        else:
                            d.self_type = n.name
                            self.visit(d)
                            body.append(d)
                    else:
                        self.visit(d)
                        body.append(d)
                fields = []
                for f in self._class_fields.values():
                    if f is not None:
                        fields.append(f)
                n.body = fields + body

        self._hierarchy_map = {}
        self._import_list = []
        self._import_count = 0

        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:    
        class_name: str = get_id(node)

        decorator_list = list(map(get_decorator_id, node.decorator_list))
        is_jlClass = "jl_class" in decorator_list

        extends = []
        if len(node.bases) == 1:
            base = node.bases[0]
            name = get_id(base)
            extends = [name]
        else:
            # TODO: Investigate Julia traits
            for base in node.bases:
                name = get_id(base)
                extends.append(name)

        self._hierarchy_map[class_name] = (extends, is_jlClass)
        node.bases += [ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        args = node.args

        for arg in args.args:
            if ((annotation := getattr(arg, "annotation", None)) and
                    (name := getattr(annotation, "id", None)) and
                    name in self._hierarchy_map):
                setattr(name, "id", f"Abstract{name}")

        if (hasattr(node, "self_type") and
                (self_type := node.self_type) in self._hierarchy_map):
            node.self_type = f"Abstract{self_type}"

        return self.generic_visit(node)

    # TODO: Rewrite special method calls
    # def visit_Call(self, node: ast.Call) -> Any:
    #     fname = node.func
    #     if fname in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
    #         pass
    #     return node

    def visit_Expr(self, node: ast.Expr) -> Any:
        parent = node.scopes[-1]
        # Initialize class expression with None type
        if isinstance(parent, ast.ClassDef) and (id := get_id(node.value)):
            self._class_fields[id] = None
        return self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> Any:
        target = node.targets[0]
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        target = node.target
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def _generic_assign_visit(self, node, target):
        if self._is_member(target):
            if target.attr not in self._class_fields:
                self._class_fields[target.attr] = node
            else:
                class_field = self._class_fields[target.attr]
                if class_field.value is None and node.value:
                    self._class_fields[target.attr] = node

    def _is_member(self, node):
        return hasattr(node, "value") and get_id(node.value) == "self"

    def visit_Import(self, node: ast.Import) -> Any:
        self._generic_import_visit(node)
        return node

    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        self._generic_import_visit(node)
        return node

    def _generic_import_visit(self, node):
        is_visit = False
        for alias in node.names:
            alias_id = get_id(alias)
            if alias_id not in self._ignored_module_set:
                is_visit = True
                if asname := getattr(alias, "asname", None):
                    self._import_list.append(asname)
                elif name := getattr(alias, "name", None):
                    self._import_list.append(name)

        if is_visit:
            self._import_count += 1

