import ast
import json
import yaml
import os
from pathlib import Path
from typing import Any, Dict, Optional

from py2many.ast_helpers import get_id
from py2many.tracer import find_node_by_type

import configparser
import logging

logger = logging.Logger("py2many")


def parse_input_configurations(filename):
    _, file_extension = os.path.splitext(filename)
    input = Path(filename)
    if not input.is_file:
        raise Exception("The input file dos not exist")
    if file_extension == ".ini":
        return ConfigFileHandler(input)
    return None


class ConfigFileHandler():
    def __init__(self, filename):
        self._config = configparser.ConfigParser()
        self._config.read(filename)
        self._parsed_defaults: Dict[str, Any] = {}
        # Parse default values, so they don't get processed multiple times
        self.parse_defaults()

    def get_sec_with_option(self, section_name, option_name):
        if not self._config.has_section(section_name):
            # logger.warn(f"No section named {section_name} was found!")
            return None
        
        section = self._config[section_name]
        if not self._config.has_option(option_name):
            # logger.warn(f"No option named {option_name} for section {section_name}!")
            return None

        return section[option_name]

    def get_section(self, section_name):
        if not self._config.has_section(section_name):
            # logger.warn(f"No section named {section_name} was found!")
            return None
        
        return self._config[section_name]

    def get_option(self, section, option_name):
        if not self._config.has_option(option_name):
            # logger.warn(f"No option named {option_name} for section {section_name}!")
            return None

        return section[option_name]

    def parse_defaults(self):
        """Gets the defaults"""
        for name, value in self._config.defaults().items():
            if name in DEFAULTS_DISPATCH_MAP:
                parsed = DEFAULTS_DISPATCH_MAP[name](self, name, value)
                self._parsed_defaults[name] = parsed

    def get_parsed_defaults(self):
        return self._parsed_defaults


class ParseAnnotations():
    """Parses annotation files"""
    def __init__(self, filename):
        self._filename = filename
        self._parsed_data = self.parse_file(filename)

    def parse_file(self, file_data):
        if file_data is not None:
            _, file_extension = os.path.splitext(file_data)
            input = Path(file_data)
            file = open(input)
            if not input.is_file:
                raise Exception(f"The configruration file {file.name} was not found.")
            elif file_extension == ".json":
                return json.load(file)
            elif file_extension == ".yaml":
                return yaml.load(file, Loader=yaml.FullLoader)
            else :
                raise Exception("Please supply either a JSON or a YAML file.")

    def retrieve_structure(self):
        file_name = str(self._filename).split(os.sep)[-1]
        class_config = {}
        if "modules" in self._parsed_data and file_name in self._parsed_data["modules"]:
            class_config = self._parsed_data["modules"][file_name]
        # Cover any general annotations that need to be applied to all files
        non_modules = dict(self._parsed_data)
        non_modules.pop("modules")
        class_config |= non_modules
        return class_config

    def get_class_attributes(self, name: str):
        if ("classes" in self._parsed_data 
            and name in self._parsed_data["classes"]):
            return self._parsed_data["classes"][name]
    
    def get_function_attributes(self, name: str, class_name: Optional[str]):
        node_field_map = {}
        if ("functions" in self._parsed_data 
                and name in (general_funcs := name["functions"])):
            node_field_map |= general_funcs

        # Check if function is in a class
        if ("classes" in self._parsed_data
                and class_name in self._parsed_data["classes"]
                and "functions" in self._parsed_data["classes"][class_name]
                and name in (class_funcs := self._parsed_data["classes"][class_name]["functions"])):
            node_field_map |= class_funcs[name]

        return node_field_map

########################################
########################################
########################################


def config_rewriters(config_handler: ConfigFileHandler, tree):
    # Handle defaults
    defaults: Dict[str, Any] = config_handler.get_parsed_defaults()
    for name, data in defaults.items():
        if name in PARSED_DISPATCH_MAP:
            PARSED_DISPATCH_MAP[name](tree, data)
    # Specific for each file 
    if ann_sec := config_handler.get_sec_with_option("annotations", tree.__file__): 
        parser = ParseAnnotations(ann_sec)
        AnnotationRewriter(parser).visit(tree)


class FlagRewriter(ast.NodeTransformer):
    def __init__(self, flags) -> None:
        super().__init__()
        self._flags = flags

    def visit_Module(self, node: ast.Module) -> Any:
        for flag_name, flag_value in self._flags:
            setattr(node, flag_name, flag_value)
        return node


class AnnotationRewriter(ast.NodeTransformer):
    def __init__(self, parser: ParseAnnotations) -> None:
        super().__init__()
        self._input_config_map = {}
        self._parser = parser
        
    def visit_Module(self, node: ast.Module) -> Any:
        self._input_config_map = self._parser.retrieve_structure()
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
                                                                        node_scope_name)

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
            node_field_map = self._parser.get_class_attributes(class_name)
            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node


DEFAULTS_DISPATCH_MAP = {
    "annotations": lambda self, name, value: ParseAnnotations(value)
}

PARSED_DISPATCH_MAP = {
    "annotations": lambda tree, parser: AnnotationRewriter(parser).visit(tree)
}