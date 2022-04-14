# Gets range from for loop
import ast
import re

from py2many.ast_helpers import get_id

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
    if isinstance(node, str):
        if parse_func:
            return parse_func(node)
        return node
    if id := get_id(node):
        if parse_func:
            return parse_func(id)
        return id
    if isinstance(node, ast.Call):
        return get_ann_repr(node.func, parse_func, default)
    if isinstance(node, ast.Attribute):
        return f"{get_ann_repr(node.value, parse_func, default)}.\
            {get_ann_repr(node.attr, parse_func, default)}"
    if isinstance(node, ast.Constant):
        if node.value:
            return node.value
        else:
            if parse_func:
                parse_func(node.value)
            else:
                return default
    if isinstance(node, ast.Subscript):
        id = get_ann_repr(node.value, parse_func, default)
        slice_val = get_ann_repr(node.slice, parse_func, default)
        return f"{id}{{{slice_val}}}"
    if isinstance(node, ast.Tuple) \
            or isinstance(node, ast.List):
        elts = []
        for e in node.elts:
            elts.append(get_ann_repr(e, parse_func, default))
        return ", ".join(elts)
    if isinstance(node, ast.Subscript):
        id = get_ann_repr(node.value, parse_func, default)
        slice_val = get_ann_repr(node.slice, parse_func, default)
        return f"{id}{{{slice_val}}}"

    return default

def get_variable_name(scope):
    common_vars = ["v", "w", "x", "y", "z"]
    new_var = None
    for var in common_vars:
        found = True
        if isinstance(scope, ast.FunctionDef):
            for arg in scope.args.args:
                if arg.arg == var:
                    found = False
                    break
        if found and (body := getattr(scope, "body", None)):
            for n in body:
                if isinstance(n, ast.Assign):
                    for x in n.targets:
                        if get_id(x) == new_var:
                            found = False
                            break
        if found:
            new_var = var
            break

    return new_var

