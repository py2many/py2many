

import ast
from py2many.ast_helpers import get_id


def parse_path(path: list[str], sep):
    """Parses a path that has been sepparated 
    (e.g using os.sep) and returns the joined 
    path using the given separator"""
    parsed_path = []
    i = 0
    while i < len(path):
        if i+1 < len(path) and path[i+1] == "..":
            i+=2
        else:
            parsed_path.append(path[i])
            i+=1
    return sep.join(parsed_path)

# Returns a string representation of the node
def get_ann_repr(node, parse_func = None, default = None, sep=["[", "]"]):
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
        if sep:
            return f"{id}{sep[0]}{slice_val}{sep[1]}"
        return f"{id}[{slice_val}]"
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