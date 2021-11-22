
import json
import yaml
import os
from pathlib import Path
from typing import Optional

class InputParser:
    def parse_file(file_data):
        if file_data is not None:
            _, file_extension = os.path.splitext(file_data)
            input = Path(file_data)
            file = open(input)
            if not input.is_file:
                raise Exception("Please supply a file.")
            if file_extension == ".json":
                return json.load(file)
            elif file_extension == ".yaml":
                return yaml.load(file, Loader=yaml.FullLoader)
            else :
                raise Exception("Please supply either a JSON or a YAML file.")

class ParseFileStructure:
    def retrieve_structure(filename: str, input_config: dict):
        file_name = str(filename).split(os.sep)[-1]
        class_config = {}
        if "modules" in input_config and file_name in input_config["modules"]:
            class_config = input_config["modules"][file_name]
        # Cover any general annotations that need to be applied to all files
        non_modules = dict(input_config)
        non_modules.pop("modules")
        class_config |= non_modules
        return class_config

    def get_class_attributes(name: str, input_config: dict):
        if ("classes" in input_config 
            and name in input_config["classes"]):
            return input_config["classes"][name]
    
    def get_function_attributes(name: str, class_name: Optional[str], input_config: dict):
        node_field_map = {}
        if ("functions" in input_config 
                and name in (general_funcs := name["functions"])):
            node_field_map |= general_funcs

        # Check if function is in a class
        if ("classes" in input_config
                and class_name in input_config["classes"]
                and "functions" in input_config["classes"][class_name]
                and name in (class_funcs := input_config["classes"][class_name]["functions"])):
            node_field_map |= class_funcs[name]

        return node_field_map
