import ast
import re
from typing import Callable, Dict, Tuple, Union

import numpy as np

from py2many.ast_helpers import get_id
from py2many.tracer import is_list


class JuliaExternalModulePlugins:
    def visit_npsum(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        dims = None
        for kwarg in kwargs:
            if kwarg[0] == "axis":
                dims = kwarg[1]
        if dims:
            return f"sum({vargs[0]}, dims={dims})"
        return f"sum({vargs[0]})"

    def visit_npwhere(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
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

    def visit_nparray(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        dtype = "Float64"
        for kwarg in kwargs:
            if kwarg[0] == "dtype":
                dtype = kwarg[1]
        if dtype in EXTERNAL_TYPE_MAP:
            dtype = EXTERNAL_TYPE_MAP[dtype](t_self)
        elems = ""
        if len(vargs) >= 1:
            elems = vargs[0]
        return f"Vector{{{dtype}}}({elems})"

    def visit_npappend(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        return f"push!({vargs[0], vargs[1]})"

    def visit_npzeros(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        zero_type = "Float64"
        for kwarg in kwargs:
            if kwarg[0] == "dtype":
                zero_type = kwarg[1]
        if zero_type in EXTERNAL_TYPE_MAP:
            # TODO: No support for custom dtype
            # https://numpy.org/doc/stable/reference/generated/numpy.zeros.html?highlight=numpy%20zeros#numpy.zeros
            zero_type = EXTERNAL_TYPE_MAP[zero_type(t_self)]

        parsed_args = []
        if node.args:
            if isinstance(node.args[0], ast.Tuple):
                parsed_args.append([t_self.visit(x) for x in node.args[0].elts])
            else:
                parsed_args.append(vargs[0])

        return f"zeros({zero_type}, {', '.join(parsed_args)})"

    def visit_npmultiply(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        # Since two elements must have same type, we just need to check one
        left = node.args[0]
        if is_list(left):
            t_self._usings.add("LinearAlgebra")
            return f"mul!({vargs[0]}, {vargs[1]})"
        return f"repeat({vargs[0]}, {vargs[1]})"

    def visit_npnewaxis(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        # TODO: Search broadcasting in Julia
        pass

    def visit_ones(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        # Default is float
        dtype = "float"
        for kwarg in kwargs:
            if kwarg[0] == "dtype":
                dtype = kwarg[1]
        if dtype == "bool":
            return f"trues{vargs[0]}"
        return f"ones({t_self._map_type(dtype)}, {vargs[0]})"

    def visit_argmax(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        axis = None
        for kwarg in kwargs:
            if kwarg[0] == "axix":
                axis = kwarg[1]
        if axis:
            if axis.isnumeric():
                axis = int(axis) + 1
            else:
                axis = f"{axis}+1"

            return f"argmax({vargs[0]}, dims={axis})"
        # By default, the index is into the flattened array
        # Therefore, we create a view over the matrix
        # Decrement 1, as Julia indexes arrays from 1
        return f"argmax(@view {vargs[0]}[:]) - 1"

    def visit_dotproduct(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        if not vargs:
            return "mult"
        match_list = lambda x: re.match(r"^list|^List|^tuple|^Tuple", x) is not None \
            if x else False
        match_scalar = lambda x: re.match(r"^int|^float|^bool", x) is not None \
            if x else False
        match_matrix = lambda x: re.match(r"^Matrix|^np.ndarray", x) is not None \
            if x else False
        # Accounts for JuliaMethodCallRewriter when getting node.args
        if t1 := getattr(node.args[1], "annotation", None):
            types_0_str = t_self.visit(t1)
        else:
            types_0_str = t_self.visit(getattr(node.scopes.find(vargs[0]), "annotation", ast.Name(id="")))
        if t2 := getattr(node.args[2], "annotation", None):
            types_1_str = t_self.visit(t2)
        else:
            types_1_str = t_self.visit(getattr(node.scopes.find(vargs[1]), "annotation", ast.Name(id="")))
        if match_list(types_0_str) and match_list(types_1_str):
            return f"({vargs[0]} ⋅ {vargs[1]})"
        elif match_scalar(types_0_str) or match_scalar(types_1_str) or \
                (match_matrix(types_0_str) and match_matrix(types_1_str)):
            return f"({vargs[0]} * {vargs[1]})"
        return f"({vargs[0]} .* {vargs[1]})"

    def visit_transpose(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]) -> str:
        t_self._usings.add("LinearAlgebra")
        return f"LinearAlgebra.transpose({', '.join(vargs)})"

    def visit_exp(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        arg = node.args[0]
        # Identify scalar operations
        if isinstance(arg, ast.Name):
            ann = node.scopes.find(vargs[0])
            if ann == "int" or ann == "float":
                return f"ℯ^{vargs[0]}"
        if isinstance(arg, ast.Constant):
            return f"ℯ^{vargs[0]}"
        return f"ℯ.^{vargs[0]}"

    def visit_reshape(t_self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str, str]]):
        if len(vargs) == 2:
            return f"reshape({vargs[0]}, {vargs[1]})"
        return "reshape"


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    np.sum: (JuliaExternalModulePlugins.visit_npsum, True),
    np.where: (JuliaExternalModulePlugins.visit_npwhere, True),
    np.array: (JuliaExternalModulePlugins.visit_nparray, True),
    np.append: (JuliaExternalModulePlugins.visit_npappend, True),
    np.zeros: (JuliaExternalModulePlugins.visit_npzeros, True),
    np.multiply: (JuliaExternalModulePlugins.visit_npmultiply, True),
    np.sqrt: (lambda self, node, vargs, kwargs: f"sqrt({vargs[0]})" if vargs else "√", True),
    np.arccos: (lambda self, node, vargs, kwargs: f"acos({vargs[0]})", True),
    np.arcsin: (lambda self, node, vargs, kwargs: f"asin({vargs[0]})", True),
    np.arctan: (lambda self, node, vargs, kwargs: f"atan({vargs[0]})", True),
    np.sin: (lambda self, node, vargs, kwargs: f"sin({vargs[0]})", True),
    np.cos: (lambda self, node, vargs, kwargs: f"cos({vargs[0]})", True),
    np.tan: (lambda self, node, vargs, kwargs: f"tan({vargs[0]})", True),
    np.newaxis: (JuliaExternalModulePlugins.visit_npnewaxis, True),  # See broadcasting
    np.ones: (JuliaExternalModulePlugins.visit_ones, True),
    np.flatnonzero: (
        lambda self, node, vargs, kwargs: f"[i-1 for (i,p) in enumerate({vargs[0]}) if p != 0]",
        True,
    ),
    np.exp: (JuliaExternalModulePlugins.visit_exp, True),
    np.argmax: (JuliaExternalModulePlugins.visit_argmax, True),
    np.shape: (lambda self, node, vargs, kwargs: f"size({vargs[0]})", True),
    np.random.randn: (lambda self, node, vargs, kwargs: f"randn({', '.join(vargs)})", True),
    np.dot: (JuliaExternalModulePlugins.visit_dotproduct, True),
    np.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.transpose: (JuliaExternalModulePlugins.visit_transpose, True),
    np.ndarray.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
    np.reshape: (JuliaExternalModulePlugins.visit_reshape, True),
    np.ndarray.shape: (lambda self, node, vargs, kwargs: f"size({vargs[0]})", True),
    # Types can also be called as functions to convert
    np.int8: (lambda self, node, vargs, kwargs: f"Int8({vargs[0]})", True),
    np.int16: (lambda self, node, vargs, kwargs: f"Int16({vargs[0]})", True),
    np.int32: (lambda self, node, vargs, kwargs: f"Int32({vargs[0]})", True),
    np.int64: (lambda self, node, vargs, kwargs: f"Int64({vargs[0]})", True),
}

# Numpy Types
EXTERNAL_TYPE_MAP = {
    np.int8: lambda self: "Int8",
    np.int16: lambda self: "Int16",
    np.int32: lambda self: "Int32",
    np.int64: lambda self: "Int64",
    np.float16: lambda self: "Float16",
    np.float32: lambda self: "Float32",
    np.float64: lambda self: "Float64",
    np.bool8: lambda self: "Bool",
    np.byte: lambda self: "UInt8",
    np.short: lambda self: "Int8",
    np.ndarray: lambda self: "Matrix",
    np.array: lambda self: "Vector",
}

class FuncTypeDispatch():
    def visit_npdot(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
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
        types_0 = getattr(vargs[0], "annotation", None)
        types_1 = getattr(vargs[1], "annotation", None)
        types_0_str = ast.unparse(types_0) if types_0 else ""
        types_1_str = ast.unparse(types_1) if types_1 else ""
        if match_list(types_0_str) and match_list(types_1_str):
            return "list"
        elif (m0 := match_scalar(types_0_str)) or (m1 := match_scalar(types_1_str)):
            return types_0_str if m0 else types_1_str
        elif (match_matrix(types_0_str) and match_list(types_1_str)) or \
                (match_matrix(types_1_str) and match_list(types_0_str)):
            return "list"
        return "np.ndarray"

FUNC_TYPE_MAP = {
    np.random.randn: lambda self, node, vargs, kwargs: "np.ndarray",
    np.sqrt: lambda self, node, vargs, kwargs: "float",
    np.dot: FuncTypeDispatch.visit_npdot,
    np.zeros: lambda self, node, vargs, kwargs: "np.ndarray",
    np.exp: lambda self, node, vargs, kwargs: "np.ndarray",
    np.transpose: lambda self, node, vargs, kwargs: "np.ndarray",
    np.ndarray.transpose: lambda self, node, vargs, kwargs: "np.ndarray",
}


IGNORED_MODULE_SET = set(["numpy"])
