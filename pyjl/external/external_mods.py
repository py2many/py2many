import importlib
import os

MOD_DIR = "pyjl/external/modules"

# Alternative: ("plugins", [(_small_dispatch_map, "SMALL_DISPATCH_MAP"), ...]
# This accounts for the self names (or just add "_" and lowercase)
EXTENSION_EXTRACT_MAP = [
    ("plugins", ["SMALL_DISPATCH_MAP", "MODULE_DISPATCH_TABLE", "FUNC_DISPATCH_TABLE"]),
    ("clike", ["JL_IGNORED_MODULE_SET"])
]


# TODO: change self arguments instead of global lists (Just add to clike)
def import_external_modules(t_self, external_mods: list[str]):
    """Updates all the dispatch maps to account for external modules"""
    for mod_name in external_mods:
        for ext_name, vals in EXTENSION_EXTRACT_MAP:
            full_mod_name = f"{MOD_DIR}/{mod_name}_{ext_name}"
            if os.path.isfile(full_mod_name):
                ext_mod = importlib.import_module(full_mod_name)
                for val in vals:
                    obj = ext_mod.__dict__[val]
                    if val in t_self.__dict__:
                        # Update value in default containers
                        curr_val = t_self.__dict__[val]
                        if isinstance(curr_val, dict):
                            curr_val |= obj
                        elif isinstance(curr_val, list):
                            curr_val.extend(obj)
                        elif isinstance(curr_val, set):
                            curr_val.intersection_update(obj)


class ExternalWrapper():
    """Wrapper to add external modules"""
    def __init__(self):
        import_external_modules(self)