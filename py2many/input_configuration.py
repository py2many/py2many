import ast
import json
import re
import yaml
import os
from pathlib import Path
from typing import Any, Dict

from py2many.ast_helpers import get_id

import configparser
import logging

logger = logging.Logger("py2many")


def parse_input_configurations(filename):
    _, file_extension = os.path.splitext(filename)
    input = Path(filename)
    if not input.is_file():
        raise Exception("The input configuration file does not exist")
    if file_extension == ".ini":
        return ConfigFileHandler(input)
    else:
        raise Exception("Configuration file has to be a .ini file")


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
        if not self._config.has_option(section.name, option_name):
            # logger.warn(f"No option named {option_name} for section {section_name}!")
            return None

        return section[option_name]

    def get_section(self, section_name):
        if not self._config.has_section(section_name):
            # logger.warn(f"No section named {section_name} was found!")
            return None
        
        return self._config[section_name]

    def get_option(self, section: configparser.SectionProxy, option_name):
        if not self._config.has_option(section.name, option_name):
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
    """Parses annotation files. If filename is None, it will look for generic annotations only"""
    def __init__(self, annotation_filename, filename=None):
        self._parsed_data = self.parse_file(annotation_filename, filename)

    def parse_file(self, annotation_filename, filename):
        """Parses the data. If filename is present, it will get 
           the data from the corresponding module"""
        if annotation_filename is not None:
            _, file_extension = os.path.splitext(annotation_filename)
            input = Path(annotation_filename)
            file = open(input)
            file_data = None
            if not input.is_file:
                raise Exception(f"The configruration file {file.name} was not found.")
            elif file_extension == ".json":
                file_data = json.load(file)
            elif file_extension == ".yaml":
                file_data = yaml.load(file, Loader=yaml.FullLoader)
            else:
                raise Exception("Please supply either a JSON or a YAML file.")

            # Get corresponding data
            module_config = {}
            if filename:
                search_file_name = str(filename).split(os.sep)[-1]
                if "modules" in file_data and search_file_name in file_data["modules"]:
                    module_config = file_data["modules"][search_file_name]
            # Cover any general annotations that need to be applied to all files
            non_modules = dict(file_data)
            non_modules.pop("modules")
            module_config |= non_modules

            return module_config


    def get_attributes(self, node: ast.AST):
        node_field_map = {}
        name = get_id(node)
        lookup_name = "functions" \
            if type(node) == ast.FunctionDef else "classes"

        # Get top level annotations
        if (lookup_name in self._parsed_data 
                and name in (general_funcs := self._parsed_data[lookup_name])):
            node_field_map |= general_funcs

        # Get fields
        temp_dict = self._parsed_data

        for scope in node.scopes[1:]:
            if isinstance(scope, ast.ClassDef) and \
                    "classes" in temp_dict and \
                    get_id(scope) in temp_dict["classes"]:
                temp_dict = temp_dict["classes"][get_id(scope)]
            if isinstance(scope, ast.FunctionDef) and \
                    "functions" in temp_dict and \
                    get_id(scope) in temp_dict["functions"]:
                temp_dict = temp_dict["functions"][get_id(scope)]

        if temp_dict and temp_dict != self._parsed_data:
            node_field_map |= temp_dict

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
    filename = re.sub("(.*)\\.(.*)", "\\1", tree.__file__.name)
    if ann_sec := config_handler.get_sec_with_option("ANNOTATIONS", filename):
        parser = ParseAnnotations(ann_sec, filename)
        AnnotationRewriter(parser).visit(tree)
    if ann_sec := config_handler.get_sec_with_option("ANNOTATIONS", "generic"):
        # Generic annotation files
        parser = ParseAnnotations(ann_sec, "generic")
        AnnotationRewriter(parser).visit(tree)

    # Input flags
    if flags := config_handler.get_section("FLAGS"):
        FlagRewriter(flags).visit(tree)


class FlagRewriter(ast.NodeTransformer):
    def __init__(self, flags):
        super().__init__()
        self._flags: Dict = flags

    def visit_Module(self, node: ast.Module) -> Any:
        for flag_name, flag_value in self._flags.items():
            flag_type = None
            if flag_value in {"True", "False"}:
                flag_type = eval(flag_value)
                if not hasattr(node, flag_name):
                    setattr(node, flag_name, flag_type)
            else:
                raise Exception("Flag values can either be 'True' or 'False'")
        return node


class AnnotationRewriter(ast.NodeTransformer):
    def __init__(self, parser: ParseAnnotations):
        super().__init__()
        self._parser = parser

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)
        node_field_map = self._parser.get_attributes(node)
        if "decorators" in node_field_map:
            node.decorator_list += node_field_map["decorators"]
            # Remove duplicates
            node.decorator_list = list(set(node.decorator_list))
            # Transform in Name nodes
            node.decorator_list = list(
                map(lambda dec: ast.Name(id=dec), node.decorator_list))

        if "args" in node_field_map:
            args_map = node_field_map["args"]
            for arg in node.args.args:
                if arg.arg in args_map:
                    arg.annotation = ast.Name(args_map[arg.arg])
        return node

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        node_field_map = self._parser.get_attributes(node)
        if node_field_map and "decorators" in node_field_map:
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