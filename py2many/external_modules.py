from dataclasses import dataclass
import os
import imp
from pydoc import ispath
from types import ModuleType

MOD_DIR = f"external{os.sep}modules"

# Alternative: ("plugins", [(_small_dispatch_map, "SMALL_DISPATCH_MAP"), ...]
# This accounts for the self names (or just add "_" and lowercase)
MOD_NAMES = set(
    [
        ("_dispatch_map", "DISPATCH_MAP"),
        ("_small_dispatch_map", "SMALL_DISPATCH_MAP"),
        ("_module_dispatch_table", "MODULE_DISPATCH_TABLE"),
        ("_func_dispatch_table", "FUNC_DISPATCH_TABLE"),
        ("_ignored_module_set", "IGNORED_MODULE_SET"),
        ("_external_type_map", "EXTERNAL_TYPE_MAP"),
        ("_func_type_map", "FUNC_TYPE_MAP"),
    ]
)

LANG_MAP = {
    "python": "py2py",
    "cpp": "pycpp",
    "dart": "pydart",
    "go": "pygo",
    "julia": "pyjl",
    "kotlin": "pykt",
    "nim": "pynim",
    "rust": "pyrs",
    "smt": "pysmt",
    "v": "pyv",
}


@dataclass
class ExternalBase():
    """Base class to add external modules"""

    def import_external_modules(self, lang):
        """Updates all the dispatch maps to account for external modules"""
        external_mods: list[tuple[str, str]] = self._get_external_modules(lang)
        if external_mods:
            for mod_path in external_mods:
                split_name: tuple[str, str] = os.path.split(mod_path)
                mod_name = split_name[1]
                ext_mod: ModuleType = imp.load_source(mod_name, mod_path)
                for attr_name, map_name in MOD_NAMES:
                    if attr_name in self.__dict__ and map_name in ext_mod.__dict__:
                        obj = ext_mod.__dict__[map_name]
                        curr_val = getattr(self, attr_name, None)
                        # Update value in default containers
                        if isinstance(curr_val, dict):
                            curr_val |= obj
                        elif isinstance(curr_val, list):
                            curr_val.extend(obj)
                        elif isinstance(curr_val, set):
                            curr_val.update(obj)


    def _get_external_modules(self, lang) -> list[tuple[str, str]]:
        p_lang = lang
        if lang in LANG_MAP:
            p_lang = LANG_MAP[lang]
        else:
            raise Exception(f"Language not supported: {lang}")
        # Get files
        path = f"{os.getcwd()}{os.sep}{p_lang}{os.sep}{MOD_DIR}"
        if not os.path.isdir(path):
            return None
        return [
            f"{path}{os.sep}{file}"
            for file in os.listdir(path)
            if os.path.isfile(os.path.join(path, file)) and file != "__init__.py"
        ]
