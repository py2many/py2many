
import json
from pathlib import Path
from typing import Dict, List

def parse_json(json_data) :
    if json_data is not None:
        json_input_config = Path(json_data)
        json_file = open(json_data)
        if not json_input_config.is_file:
            raise Exception("Please supply a JSON file.")
        return json.load(json_file)

    return None
