# Gets range from for loop
import ast
import subprocess
import os
import random
from typing import Optional

from py2many.ast_helpers import get_id
from py2many.helpers import get_ann_repr
from py2many.scope import ScopeList

from py2many.tracer import find_node_by_name_and_type
from pyjl.global_vars import SEP

# TODO: Currently not in use
def get_range_from_for_loop(node):
    iter = 0
    if hasattr(node.iter, "args") and node.iter.args:
        if len(node.iter.args) > 1:
            start_val = node.iter.args[0]
            end_val = node.iter.args[1]
        else:
            start_val = 0
            end_val = node.iter.args[0]

        # If they are name nodes, search for their values
        if isinstance(end_val, ast.Name):
            end_val = find_node_by_name_and_type(
                get_id(end_val), (ast.Assign, ast.AnnAssign, ast.AugAssign), node.scopes
            )[0]
            if end_val is not None:
                end_val = end_val.value
        if isinstance(start_val, ast.Name):
            start_val = find_node_by_name_and_type(
                get_id(start_val),
                (ast.Assign, ast.AnnAssign, ast.AugAssign),
                node.scopes,
            )[0]
            if start_val is not None:
                start_val = start_val.value

        # Iter value cannot be calculated
        if not isinstance(start_val, (ast.Constant, int, str)) or not isinstance(
            end_val, (ast.Constant, int, str)
        ):
            return 0

        # Calculate iter value
        start_val = get_ann_repr(start_val, sep=SEP)
        end_val = get_ann_repr(end_val, sep=SEP)
        if not isinstance(start_val, int):
            start_val = int(start_val)
        if not isinstance(end_val, int):
            end_val = int(end_val)

        iter += end_val - start_val

        if iter < 0:
            iter *= -1
    return iter


# Gets a new name for a variable
def generate_var_name(node, possible_names: list[str], prefix=None, suffix=None):
    final_name = None
    for name in possible_names:
        final_name = _apply_prefix_and_suffix(name, prefix, suffix)
        if not node.scopes.find(final_name):
            break
        else:
            final_name = None

    while not final_name:
        r = random.randint(100, 999)
        final_name = _apply_prefix_and_suffix(f"{name}_{r}", prefix, suffix)
        if not node.scopes.find(final_name):
            break
        else:
            final_name = None

    return final_name


# Applies prefix and suffix
def _apply_prefix_and_suffix(name: str, prefix, suffix):
    new_name = name
    if prefix:
        new_name = f"{prefix}_{name}"
    if suffix:
        new_name = f"{name}_{suffix}"
    return new_name


def get_func_def(node, name):
    if not hasattr(node, "scopes"):
        return None

    func_def = find_node_by_name_and_type(name, ast.FunctionDef, node.scopes)[0]
    if func_def:
        return func_def

    assign = find_node_by_name_and_type(name, ast.Assign, node.scopes)[0]
    if assign and (assign_val := assign.value):
        assign_id = None
        if assign_val and isinstance(assign_val, ast.Call):
            assign_id = get_id(assign_val.func)
        elif id := get_id(assign_val):
            assign_id = id
        return find_node_by_name_and_type(assign_id, ast.FunctionDef, node.scopes)[0]
    return None


def obj_id(node):
    """A wrapper arround the get_id function to cover attributes"""
    if isinstance(node, ast.Attribute):
        return node.attr
    return get_id(node)


DEFAULTS_TABLE = {
    "int": lambda scopes: ast.Constant(value=0, scopes=scopes),
    "float": lambda scopes: ast.Constant(value=0.0, scopes=scopes),
    "list": lambda scopes: ast.List(elts=[], ctx=ast.Load()),
    "List": lambda scopes: ast.List(elts=[], ctx=ast.Load()),
    "Dict": lambda scopes: ast.Dict(keys=[], values=[], ctx=ast.Load()),
    "set": lambda scopes: ast.Call(
        func=ast.Name(id="set", ctx=ast.Load()), args=[], keywords=[], scopes=scopes
    ),
}


def get_default_val(node, ann):
    scopes = getattr(node, "scopes", ScopeList())
    if (id := get_id(ann)) in DEFAULTS_TABLE:
        return DEFAULTS_TABLE[id](scopes)
    elif isinstance(ann, ast.Subscript) and (id := get_id(ann.value)) in DEFAULTS_TABLE:
        return DEFAULTS_TABLE[id](scopes)
    return ast.Constant(value=None)


def fill_attributes(
    node, scopes, no_rewrite=False, preserve_keyword=False, is_annotation=False
):
    ast.fix_missing_locations(node)
    node.scopes = scopes
    if no_rewrite:
        node.no_rewrite = no_rewrite
    if preserve_keyword:
        node.preserve_keyword = preserve_keyword
    if is_annotation:
        if isinstance(node, ast.Call):
            node.func.is_annotation = is_annotation
        node.is_annotation = is_annotation
    return node

def pycall_import(self, node: ast.Call, mod_name: str, opt_name: Optional[str] = None):
    self._usings.add("PyCall")
    if opt_name:
        self._pycall_imports.add(opt_name)
        import_stmt = f'{opt_name} = pyimport("{mod_name}")'
    else:
        self._pycall_imports.add(mod_name)
        import_stmt = f'{mod_name} = pyimport("{mod_name}")'
    self._globals.add(import_stmt)

def get_python_dll_path(version: tuple[str, str]):
    """Receives major and minor version information 
    and returns the corresponding Python DLL path"""
    if len(version) != 2:
        return None
    # Checks the path of the dll for Python 
    # given a version number
    version_str = f"{version[0]}{version[1]}"
    python_path = subprocess.check_output(f'where python{version_str}.dll').decode().strip().split("\n")
    python_path = python_path[1] \
        if len(python_path) > 1 \
        else python_path[0]
    return f"\"{'/'.join(python_path.strip().split(os.sep))}\""

def get_python_exe_path():
    """Returns the Python exe path"""
    python_path = subprocess.check_output(f'where python.exe').decode().strip().split("\n")
    python_path = python_path[1] \
        if len(python_path) > 1 \
        else python_path[0]
    return f"\"{'/'.join(python_path.strip().split(os.sep))}\""
