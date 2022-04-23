import json
import yaml
import os
from pathlib import Path
from typing import Any, Dict, Optional

import configparser
import logging

logger = logging.Logger("pyjl")


def parse_input_configurations(filename):
    _, file_extension = os.path.splitext(filename)
    input = Path(filename)
    if not input.is_file:
        raise Exception("The input file dos not exist")
    elif file_extension == ".ini":
        return ConfigFileHandler(input)


class ConfigFileHandler():
    def __init__(self, filename) -> None:
        self._config = configparser.ConfigParser()
        self._config.read(filename)
        self._parsed_defaults: Dict[str, Any] = {}
        # Parse default values
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
        """Gets the supported defaults"""
        default_sec = self.get_section("DEFAULT")
        if option := self.get_option(default_sec, "annotations"):
            parsed_annotations = ParseAnnotations(option)
            self._parsed_defaults["annotations"] = parsed_annotations

    def get_default(self, default_name):
        if default_name in self._parsed_defaults:
            return self._parsed_defaults[default_name]
        else:
            return None


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


