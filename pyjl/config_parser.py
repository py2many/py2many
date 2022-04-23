
import ast
from typing import Any, Dict
from py2many.ast_helpers import get_id

from py2many.input_configuration import ConfigFileHandler, ParseAnnotations
from py2many.tracer import find_node_by_type


# TODO: Optimize: The init and annotation files are parsed for every module
def julia_config_parser(tree, input_config: ConfigFileHandler):
    if ann_sec := input_config.get_section("annotations"):
        # TODO: Could be per file
        if input_config.get_option(ann_sec, "default"):
            parser = ParseAnnotations(input_config.get_option(ann_sec, "default"))
            JuliaAnnotationRewriter(parser).visit(tree)
    if flags := input_config.get_section("annotations"):
        flags.items()


class JuliaFlagRewriter(ast.NodeTransformer):
    def __init__(self, flags) -> None:
        super().__init__()
        self._flags = flags

    def visit_Module(self, node: ast.Module) -> Any:
        for flag_name, flag_value in self._flags:
            setattr(node, flag_name, flag_value)
        return node


class JuliaAnnotationRewriter(ast.NodeTransformer):
    def __init__(self, parser: ParseAnnotations) -> None:
        super().__init__()
        self._input_config_map = {}
        self._parser = parser
        
    def visit_Module(self, node: ast.Module) -> Any:
        self._input_config_map = self._parser.retrieve_structure(node.__file__, self._input_config)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)
        node_name = get_id(node)
        node_scope_name = None
        if self._input_config_map:
            if len(node.scopes) > 2:
                node_class = find_node_by_type(ast.ClassDef, node.scopes)
                node_scope_name = get_id(node_class) if node_class else None

            node_field_map = self._parser.get_function_attributes(node_name,
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
            node_field_map = self._parser.get_class_attributes(
                class_name, self._input_config_map)
            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node