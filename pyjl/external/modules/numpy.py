import ast
from typing import Callable, Dict, Tuple, Union

import numpy as np

from py2many.ast_helpers import get_id
from py2many.tracer import is_list


class JuliaExternalModulePlugins:
    def visit_npsum(t_self, node: ast.Call, vargs) -> str:
        dims = None
        for k in node.keywords:
            if k.arg == "axis":
                dims = JuliaExternalModulePlugins._visit_val(t_self, k.value)
        if dims:
            return f"sum({vargs[0]}, dims={dims})"
        return f"sum({vargs[0]})"

    def visit_npwhere(t_self, node: ast.Call, vargs: list[str]) -> str:
        if len(vargs) == 3:
            return f"@. ifelse({vargs[0]}, {vargs[1]}, {vargs[2]})"
        else:
            condition = node.args[1]
            loop_var = None
            if isinstance(condition, ast.Compare):
                if isinstance(condition.left, ast.Name):
                    loop_var = get_id(condition.left)
            if loop_var:
                var_name = "np_x"
                return f"""[{var_name} for {var_name} in {loop_var} if {vargs[1]}]"""

    def visit_nparray(t_self, node: ast.Call, vargs: list[str]) -> str:
        if len(vargs) > 0:
            return vargs[0]
        return "[]"

    def visit_npappend(t_self, node: ast.Call, vargs: list[str]) -> str:
        return f"push!({vargs[0], vargs[1]})"

    def visit_npzeros(t_self, node: ast.Call, vargs: list[str]) -> str:
        zero_type = "Float64"
        for k in node.keywords:
            # TODO: No support for custom dtype
            # https://numpy.org/doc/stable/reference/generated/numpy.zeros.html?highlight=numpy%20zeros#numpy.zeros
            if "dtype" == k.arg:
                zero_type = JuliaExternalModulePlugins._visit_val(t_self, k.value)
        
        parsed_args = []
        if node.args:
            if isinstance(node.args[0], ast.Tuple):
                parsed_args.append([t_self.visit(x) for x in node.args[0].elts])
            else:
                parsed_args.append(vargs[0])

        return f"zeros({zero_type}, {', '.join(parsed_args)})"

    def visit_npmultiply(t_self, node: ast.Call, vargs: list[str]) -> str:
        # Since two elements must have same type, we just need to check one
        left = node.args[0]
        if is_list(left):
            t_self._usings.add("LinearAlgebra")
            return f"mul!({vargs[0]}, {vargs[1]})"
        return f"{vargs[0]}*{vargs[1]}"

    def _visit_val(t_self, node):
        if isinstance(node, ast.Constant):
            return t_self.visit_Constant(node, quotes=False)
        else:
            return t_self.visit(node)


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    np.sum: (JuliaExternalModulePlugins.visit_npsum, True),
    np.where: (JuliaExternalModulePlugins.visit_npwhere, True),
    np.array: (JuliaExternalModulePlugins.visit_nparray),
    np.append: (JuliaExternalModulePlugins.visit_npappend),
    np.zeros: (JuliaExternalModulePlugins.visit_npzeros),
    np.multiply: (JuliaExternalModulePlugins.visit_npmultiply),
    np.sqrt: (lambda self, node, vargs: f"√({vargs[0]})", False),
    np.arccos: (lambda self, node, vargs: f"acos({vargs[0]})", False),
    np.arcsin: (lambda self, node, vargs: f"asin({vargs[0]})", False),
    np.arctan: (lambda self, node, vargs: f"atan({vargs[0]})", False),
    np.sin: (lambda self, node, vargs: f"sin({vargs[0]})", False),
    np.cos: (lambda self, node, vargs: f"cos({vargs[0]})", False),
    np.tan: (lambda self, node, vargs: f"tan({vargs[0]})", False),
    np.newaxis: (JuliaExternalModulePlugins.visit_npnewaxis), # See broadcasting
}

# Numpy Types
EXTERNAL_TYPE_MAP = {
    np.int8: "Int8",
    np.int16: "Int16",
    np.int32: "Int32",
    np.int64: "Int64",
    np.int128: "BigInt",
    np.int256: "BigInt",
    np.float16: "Float16",
    np.float32: "Float32",
    np.float64: "Float64",
    np.float128: "BigFloat",
    np.float256: "BigFloat",
    np.bool8: "Bool",
    np.byte: "UInt8",
    np.short: "Int8",
}

FUNC_TYPE_MAP = {
    "numpy.multiply": "list",
    "numpy.sum": "list",
    "numpy.append": "list"
}