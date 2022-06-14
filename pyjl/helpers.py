# Gets range from for loop
import ast
import os
from random import Random
import random
import re

from py2many.ast_helpers import get_id
from py2many.scope import ScopeList

from py2many.tracer import find_node_by_name_and_type

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
            end_val = find_node_by_name_and_type(get_id(end_val), 
                (ast.Assign, ast.AnnAssign, ast.AugAssign), node.scopes)[0]
            if end_val is not None: end_val = end_val.value
        if isinstance(start_val, ast.Name):
            start_val = find_node_by_name_and_type(get_id(start_val), 
                (ast.Assign, ast.AnnAssign, ast.AugAssign), node.scopes)[0]
            if start_val is not None: start_val = start_val.value

        # Iter value cannot be calculated
        if (not isinstance(start_val, (ast.Constant, int, str)) or 
                not isinstance(end_val, (ast.Constant, int, str))):
            return 0

        # Calculate iter value
        start_val = get_ann_repr(start_val)
        end_val = get_ann_repr(end_val)
        if not isinstance(start_val, int): 
            start_val = int(start_val)
        if not isinstance(end_val, int):
            end_val = int(end_val)

        iter += end_val - start_val

        if(iter < 0):
            iter *= -1
    return iter

# Returns a string representation of the node
def get_ann_repr(node, parse_func = None, default = None):
    if node == None:
        return default
    elif isinstance(node, str):
        if parse_func:
            return parse_func(node)
        return node
    elif id := get_id(node):
        if parse_func:
            return parse_func(id)
        return id
    elif isinstance(node, ast.Call):
        func = get_ann_repr(node.func, parse_func, default)
        args = []
        for arg in node.args:
            args.append(get_ann_repr(arg, parse_func, default))
        return f"{'.'.join(args)}.{func}"
    elif isinstance(node, ast.Attribute):
        return f"{get_ann_repr(node.value, parse_func, default)}.\
            {get_ann_repr(node.attr, parse_func, default)}"
    elif isinstance(node, ast.Constant):
        return ast.unparse(node)
    elif isinstance(node, ast.Subscript):
        id = get_ann_repr(node.value, parse_func, default)
        slice_val = get_ann_repr(node.slice, parse_func, default)
        return f"{id}{{{slice_val}}}"
    elif isinstance(node, ast.Tuple) \
            or isinstance(node, ast.List):
        elts = list(map(lambda x: get_ann_repr(x, parse_func, default), node.elts))
        return ", ".join(elts)
    elif ann := ast.unparse(node):
        # Not in expected cases
        if parse_func and (parsed_ann := parse_func(ann)):
            return parsed_ann
        return ann

    return default

# def get_variable_name(scope):
#     common_vars = ["v", "w", "x", "y", "z"]
#     new_var = None
#     for var in common_vars:
#         found = True
#         if isinstance(scope, ast.FunctionDef):
#             for arg in scope.args.args:
#                 if arg.arg == var:
#                     found = False
#                     break
#         if found and (body := getattr(scope, "body", None)):
#             for n in body:
#                 if isinstance(n, ast.Assign):
#                     for x in n.targets:
#                         if get_id(x) == new_var:
#                             found = False
#                             break
#         if found:
#             new_var = var
#             break

#     return new_var

# Gets a new name for a variable
def generate_var_name(node, possible_names: list[str], prefix = None, suffix = None):
    final_name = None
    for name in possible_names:
        final_name = _apply_prefix_and_suffix(name, prefix, suffix)
        if not node.scopes.find(final_name):
            break
        else:
            final_name = None

    while not final_name:
        r = random.randint(100,999)
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
        elif id:= get_id(assign_val):
            assign_id = id
        return find_node_by_name_and_type(assign_id, ast.FunctionDef, node.scopes)[0]
    return None


def obj_id(node):
        """A wrapper arround the get_id function to cover attributes"""
        if isinstance(node, ast.Attribute):
            return node.attr
        return get_id(node)

def _parse_path(import_name: str, basedir) -> str:
        cwd = os.getcwd().split(os.sep)
        base_dir = basedir.as_posix().split("/")
        if os.path.isfile(basedir.as_posix()):
            base_dir = base_dir[:-1]
        path = import_name.split(".")
        indexes = [idx for idx, elem in enumerate(base_dir) if elem in path]
        if indexes and (idx := indexes[0]) < len(base_dir):
            full_path = cwd + base_dir[0:idx+1] + path
        else:
            full_path = cwd + base_dir + path
        parsed_path = []
        i = 0
        while i < len(full_path):
            if i+1 < len(full_path) and full_path[i+1] == "..":
                i+=2
            else:
                parsed_path.append(full_path[i])
                i+=1
        return os.sep.join(parsed_path)

def is_file(path: str, basedir, extension="py"):
    """Takes a dot separated file path"""
    maybe_path = _parse_path(path, basedir)
    return os.path.isfile(f"{maybe_path}.{extension}")

def is_dir(path: str, basedir):
    """Takes a dot separated directory path"""
    maybe_path = _parse_path(path, basedir)
    return os.path.isdir(maybe_path)

DEFAULTS_TABLE = {
    "int": lambda scopes: ast.Constant(value = 0, scopes = scopes),
    "float": lambda scopes: ast.Constant(value = 0.0, scopes = scopes),
    "list": lambda scopes: ast.List(elts=[], ctx=ast.Load()),
    "List": lambda scopes: ast.List(elts=[], ctx=ast.Load()),
    "Dict": lambda scopes: ast.Dict(keys=[], values = [], ctx=ast.Load()),
    "set": lambda scopes: ast.Call( func = ast.Name(id='set', ctx=ast.Load()), 
        args = [], keywords = [], scopes = scopes)
}

def get_default_val(node, ann):
    scopes = getattr(node, "scopes", ScopeList())
    if (id := get_id(ann)) in DEFAULTS_TABLE:
        return DEFAULTS_TABLE[id](scopes)
    elif isinstance(ann, ast.Subscript) and \
            (id := get_id(ann.value)) in DEFAULTS_TABLE:
        return DEFAULTS_TABLE[id](scopes)
    return ast.Constant(value=None)