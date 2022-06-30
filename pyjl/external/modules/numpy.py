import ast
import re
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

            return f"argmax({vargs[0]}, dims={axis})"
        # By default, the index is into the flattened array
        # Therefore, we create a view over the matrix
        # Decrement 1, as Julia indexes arrays from 1
        return f"argmax(@view {vargs[0]}[:]) - 1"

    def visit_dotproduct(t_self, node: ast.Call, vargs: list[str]):
        if not vargs:
            return "mult"
        match_list = lambda x: re.match(r"^list|^List|^tuple|^Tuple", x) is not None \
            if x else False
        match_scalar = lambda x: re.match(r"^int|^float|^bool", x) is not None \
            if x else None
        match_matrix = lambda x: re.match(r"^Matrix|^np.ndarray", x) is not None \
            if x else None
        types_0_str = ast.unparse(getattr(node.args[1], "annotation", ast.Name(id="")))
        types_1_str = ast.unparse(getattr(node.args[2], "annotation", ast.Name(id="")))
        if match_list(types_0_str) and match_list(types_1_str):
            return f"({vargs[0]} ⋅ {vargs[1]})"
        elif match_scalar(types_0_str) or match_scalar(types_1_str) or \
                (match_matrix(types_0_str) and match_matrix(types_1_str)):
            return f"({vargs[0]} * {vargs[1]})"
        return f"({vargs[0]} .* {vargs[1]})"

    def visit_transpose(t_self, node: ast.Call, vargs: list[str]) -> str:
        t_self._usings.add("LinearAlgebra")
        return f"LinearAlgebra.transpose({', '.join(vargs)})"

    def visit_exp(t_self, node: ast.Call, vargs: list[str]):
        arg = node.args[0]
        # Identify scalar operations
        if isinstance(arg, ast.Name):
            ann = node.scopes.find(vargs[0])
            if ann == "int" or ann == "float":
                return f"ℯ^{vargs[0]}"
        if isinstance(arg, ast.Constant):
            return f"ℯ^{vargs[0]}"
        return f"ℯ.^{vargs[0]}"

    def visit_reshape(t_self, node: ast.Call, vargs: list[str]):
        if len(vargs) == 2:
            return f"reshape({vargs[0]}, {vargs[1]})"
        return "reshape"

    @staticmethod
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
    np.dot: (JuliaExternalModulePlugins.visit_dotproduct, True),
    np.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
    np.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
    np.ndarray.shape: (lambda self, node, vargs: f"size({vargs[0]})", True),
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
    np.ndarray: "Matrix",
    np.array: "Vector",
}

class FuncTypeDispatch():
    def visit_npdot(self, node, vargs):
        # From Python docs (https://numpy.org/doc/stable/reference/generated/numpy.dot.html?highlight=numpy%20dot#numpy.dot)
        # - If both a and b are 1-D arrays, it is inner product of vectors 
        #   (without complex conjugation).
        # - If both a and b are 2-D arrays, it is matrix multiplication, 
        #   but using matmul or a @ b is preferred.
        # - If either a or b is 0-D (scalar), it is equivalent to 
        #   multiply and using numpy.multiply(a, b) or a * b is preferred.
        # - If a is an N-D array and b is a 1-D array, it is a sum product 
        #   over the last axis of a and b.
        # - If a is an N-D array and b is an M-D array (where M>=2), it is a 
        #   sum product over the last axis of a and the second-to-last axis of b.
        match_list = lambda x: re.match(r"^list|^List|^tuple|^Tuple", x) is not None \
            if x else False
        match_scalar = lambda x: re.match(r"^int|^float|^bool", x) is not None \
            if x else None
        match_matrix = lambda x: re.match(r"^Matrix|^np.ndarray", x) is not None \
            if x else None
        types_0 = getattr(node.scopes.find(vargs[0]), "annotation", None)
        types_1 = getattr(node.scopes.find(vargs[1]), "annotation", None)
        types_0_str = self.visit(types_0) if types_0 else ""
        types_1_str = self.visit(types_1) if types_1 else ""
        if match_list(types_0_str) and match_list(types_1_str):
            return "list"
        elif (m0 := match_scalar(types_0_str)) or (m1 := match_scalar(types_1_str)):
            return types_0_str if m0 else types_1_str
        elif (match_matrix(types_0_str) and match_list(types_1_str)) or \
                (match_matrix(types_1_str) and match_list(types_0_str)):
            return "list"
        return "np.ndarray"

FUNC_TYPE_MAP = {
    np.random.randn: lambda self, node, vargs: "np.ndarray",
    np.sqrt: lambda self, node, vargs: "float",
    np.dot: FuncTypeDispatch.visit_npdot,
    np.zeros: lambda self, node, vargs: "np.ndarray",
    np.exp: lambda self, node, vargs: "np.ndarray",
    np.transpose: lambda self, node, vargs: "np.ndarray",
    np.ndarray.transpose: lambda self, node, vargs: "np.ndarray",
}


IGNORED_MODULE_SET = set(["numpy"])
