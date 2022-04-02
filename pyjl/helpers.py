# Gets range from for loop
import ast
from ctypes import Union

from libcst import FunctionDef
from py2many.ast_helpers import get_id

from py2many.tracer import find_in_body, find_node_by_name_and_type

# TODO: Delete if not necessary
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
        start_val = _get_value(start_val)
        end_val = _get_value(end_val)
        if not isinstance(start_val, int): 
            start_val = int(start_val)
        if not isinstance(end_val, int):
            end_val = int(end_val)

        iter += end_val - start_val

        if(iter < 0):
            iter *= -1
    return iter

def _get_value(node):
    if isinstance(node, ast.Constant):
        return node.value

    return node

def find_assign_value(id, scopes):
    assign = getattr(find_node_by_name_and_type(id, ast.Assign, scopes)[0], "value", None)
    ann_assign = getattr(find_node_by_name_and_type(id, ast.AnnAssign, scopes)[0], "value", None)
    return assign if assign else ann_assign

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