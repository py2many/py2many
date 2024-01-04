import ast

from .ast_helpers import get_id


# Returns a string representation of the node
def get_ann_repr(node, parse_func=None, default=None, sep=["[", "]"]):
    if node is None:
        return default
    if isinstance(node, str):
        if parse_func:
            return parse_func(node)
        return node
    elif isinstance(node, ast.Name):
        id = get_id(node)
        if parse_func:
            return parse_func(id)
        return id
    elif isinstance(node, ast.Call):
        func = get_ann_repr(node.func, parse_func, default, sep)
        args = []
        for arg in node.args:
            args.append(get_ann_repr(arg, parse_func, default, sep))
        return f"{'.'.join(args)}.{func}"
    elif isinstance(node, ast.Attribute):
        return f"{get_ann_repr(node.value, parse_func, default, sep)}.{get_ann_repr(node.attr, parse_func, default, sep)}"
    elif isinstance(node, ast.Constant):
        if parse_func:
            return parse_func(node.value)
        return f"{node.value}"
    elif isinstance(node, ast.Subscript):
        id = get_ann_repr(node.value, parse_func, default, sep)
        slice_val = get_ann_repr(node.slice, parse_func, default, sep)
        if sep:
            return f"{id}{sep[0]}{slice_val}{sep[1]}"
        return f"{id}[{slice_val}]"
    elif isinstance(node, ast.Tuple) or isinstance(node, ast.List):
        elts = list(map(lambda x: get_ann_repr(x, parse_func, default, sep), node.elts))
        return ", ".join(elts)
    elif ann := ast.unparse(node):
        # Not in expected cases
        if parse_func and (parsed_ann := parse_func(ann)):
            return parsed_ann
        return ann

    return default
