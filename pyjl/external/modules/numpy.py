import ast
from typing import Callable, Dict, Tuple, Union

import numpy as np

from py2many.ast_helpers import get_id
from py2many.tracer import is_list


class JuliaExternalModulePlugins:
    def visit_npsum(t_self, node: ast.Call, vargs: list[str]) -> str:
        dims = None
        keywords = JuliaExternalModulePlugins._get_keywords(t_self, node)
        if "axis" in keywords:
            dims = keywords["axis"]
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
        keywords = JuliaExternalModulePlugins._get_keywords(t_self, node)
        type = "Float64"
        elems = ""
        if len(vargs) >= 1:
            elems = vargs[0]
        if "dtype" in keywords:
            if keywords["dtype"] in EXTERNAL_TYPE_MAP:
                type = EXTERNAL_TYPE_MAP[keywords["dtype"]]
        return f"Vector{{{type}}}({elems})"

    def visit_npappend(t_self, node: ast.Call, vargs: list[str]) -> str:
        return f"push!({vargs[0], vargs[1]})"

    def visit_npzeros(t_self, node: ast.Call, vargs: list[str]) -> str:
        zero_type = "Float64"
        keywords = JuliaExternalModulePlugins._get_keywords(t_self, node)
        if "dtype" in keywords:
            # TODO: No support for custom dtype
            # https://numpy.org/doc/stable/reference/generated/numpy.zeros.html?highlight=numpy%20zeros#numpy.zeros
            if keywords["dtype"] in EXTERNAL_TYPE_MAP:
                zero_type = EXTERNAL_TYPE_MAP[keywords["dtype"]]
            zero_type = keywords["dtype"]

        parsed_args = []
        if node.args:
            if isinstance(node.args[0], ast.Tuple):
                parsed_args.append([t_self.visit(x) for x in node.args[0].elts])
            else:
                parsed_args.append(vargs[0])

        return f"zeros({zero_type}, {', '.join(parsed_args)})"

    def _visit_val(t_self, node: ast.Call):
        if isinstance(node, ast.Constant):
            return t_self.visit_Constant(node, quotes=False)
        else:
            return t_self.visit(node)

    def visit_npmultiply(t_self, node: ast.Call, vargs: list[str]) -> str:
        # Since two elements must have same type, we just need to check one
        left = node.args[0]
        if is_list(left):
            t_self._usings.add("LinearAlgebra")
            return f"mul!({vargs[0]}, {vargs[1]})"
        return f"repeat({vargs[0]}, {vargs[1]})"

    def visit_npnewaxis(t_self, node: ast.Call, vargs: list[str]):
        # TODO: Search broadcasting in Julia
        pass

    def visit_ones(t_self, node: ast.Call, vargs: list[str]):
        keywords = JuliaExternalModulePlugins._get_keywords(t_self, node)
        val_type = "Float64"
        if "dtype" in keywords:
            if "dtype" in EXTERNAL_TYPE_MAP:
                keywords["dtype"] in EXTERNAL_TYPE_MAP
            else:
                keywords["dtype"] = t_self._map_type(keywords["dtype"])
            val_type = keywords["dtype"]
        return f"ones({val_type}, {vargs[0]})"

    def visit_argmax(t_self, node: ast.Call, vargs: list[str]):
        keywords = JuliaExternalModulePlugins._get_keywords(t_self, node)
        axis = None
        if "axis" in keywords:
            axis: str = keywords["axis"]
            if axis.isnumeric():
                axis = int(axis) + 1
            else:
                axis = f"{axis}+1"

            return f"map(x -> x[{axis}], argmax({vargs[0]}, dims={axis})"
        return f"argmax({vargs[0]})"

    # Not really representative
    # def visit_dotproduct(t_self, node: ast.Call, vargs: list[str]):
    #     t_self._usings.add("LinearAlgebra")
    #     return f"LinearAlgebra.dot({', '.join(vargs)})"

    def visit_transpose(t_self, node: ast.Call, vargs: list[str]) -> str:
        t_self._usings.add("LinearAlgebra")
        return f"LinearAlgebra.transpose({', '.join(vargs)})"

    def visit_exp(t_self, node: ast.Call, vargs: list[str]):
        arg = node.args[0]
        if isinstance(arg, ast.Name):
            ann = node.scopes.find(arg)
            if ann == "int" or ann == "float":
                return f"ℯ^{vargs[0]}"
        if isinstance(arg, ast.Constant):
            return f"ℯ^{vargs[0]}"
        return f"ℯ.^{vargs[0]}"

    def visit_reshape(t_self, node: ast.Call, vargs: list[str]):
        if len(vargs) == 2:
            return f"reshape({vargs[0]}, {vargs[1]})"
        return "reshape"

    def _get_keywords(t_self, node: ast.Call):
        return {
            k.arg: (JuliaExternalModulePlugins._visit_val(t_self, k.value))
            for k in node.keywords
        }


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    np.sum: (JuliaExternalModulePlugins.visit_npsum, True),
    np.where: (JuliaExternalModulePlugins.visit_npwhere, True),
    np.array: (JuliaExternalModulePlugins.visit_nparray, True),
    np.append: (JuliaExternalModulePlugins.visit_npappend, True),
    np.zeros: (JuliaExternalModulePlugins.visit_npzeros, True),
    np.multiply: (JuliaExternalModulePlugins.visit_npmultiply, True),
    np.sqrt: (lambda self, node, vargs: f"sqrt({vargs[0]})" if vargs else "√", True),
    np.arccos: (lambda self, node, vargs: f"acos({vargs[0]})", True),
    np.arcsin: (lambda self, node, vargs: f"asin({vargs[0]})", True),
    np.arctan: (lambda self, node, vargs: f"atan({vargs[0]})", True),
    np.sin: (lambda self, node, vargs: f"sin({vargs[0]})", True),
    np.cos: (lambda self, node, vargs: f"cos({vargs[0]})", True),
    np.tan: (lambda self, node, vargs: f"tan({vargs[0]})", True),
    np.newaxis: (JuliaExternalModulePlugins.visit_npnewaxis, True),  # See broadcasting
    np.ones: (JuliaExternalModulePlugins.visit_ones, True),
    np.flatnonzero: (
        lambda self, node, vargs: f"[i for i in (0:length({vargs[0]})-1) if {vargs[0]}[i+1] != 0]",
        True,
    ),
    np.exp: (JuliaExternalModulePlugins.visit_exp, True),
    np.argmax: (JuliaExternalModulePlugins.visit_argmax, True),
    np.shape: (lambda self, node, vargs: f"size({vargs[0]})", True),
    np.random.randn: (lambda self, node, vargs: f"randn({', '.join(vargs)})", True),
    np.dot: (
        lambda self, node, vargs: f"({vargs[0]} .* {vargs[1]})" if vargs else "mult",
        True,
    ),
    np.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
    np.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
}

# Numpy Types
EXTERNAL_TYPE_MAP = {
    np.int8: "Int8",
    np.int16: "Int16",
    np.int32: "Int32",
    np.int64: "Int64",
    np.float16: "Float16",
    np.float32: "Float32",
    np.float64: "Float64",
    np.bool8: "Bool",
    np.byte: "UInt8",
    np.short: "Int8",
}

# TODO: Results in wrong function annotations
FUNC_TYPE_MAP = {
    # "numpy.multiply": "list",
    # "numpy.sum": "list",
    # "numpy.append": "list",
    # "numpy.sqrt": "float",
    # "np.dot": "float",
    # "np.zeros": "np.ndarray",
    "numpy.exp": "list"
}


IGNORED_MODULE_SET = set(["numpy"])
