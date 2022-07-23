import ctypes
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_load_library(self, node, vargs):
        self._usings.add("Libdl")
        return f"Libdl.dlopen({vargs[0]})" if vargs else "Libdl.dlopen"

    def visit_cdll(self, node, vargs):
        self._usings.add("Libdl")
        return f"Libdl.dlopen({vargs[0]})" if vargs else "Libdl.dlopen"

    def visit_cast(self, node, vargs):
        self._usings.add("Libdl")
        return f"cast({vargs[0]}, {self._map_type(vargs[1])})"


FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    ctypes.cdll.LoadLibrary: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.CDLL: (JuliaExternalModulePlugins.visit_cdll, True),
    ctypes.cast: (JuliaExternalModulePlugins.visit_cast, True),
}

EXTERNAL_TYPE_MAP = {
    ctypes.c_int: "Cint",
    ctypes.c_int8: "Cint",
    ctypes.c_int16: "Cint",
    ctypes.c_int32: "Cint",
    ctypes.c_int64: "Cint",
    ctypes.c_uint8: "Cuint",
    ctypes.c_uint16: "Cuint",
    ctypes.c_uint32: "Cuint",
    ctypes.c_uint64: "Cuint",
    ctypes.c_bool: "Cbool",
    ctypes.c_float: "Cfloat",
    ctypes.c_double: "Cdouble",
    ctypes.c_short: "Cshort",
    ctypes.c_ushort: "Cushort",
    ctypes.c_long: "Clong",
    ctypes.c_ulong: "Culong",
    ctypes.c_longlong: "Clonglong",
    ctypes.c_ulonglong: "Culonglong",
    # ctypes.c_longdouble: "", # No mapping
    ctypes.c_byte: "Cuint", # TODO: Check this
    ctypes.c_ubyte: "Cuint", # TODO: Check this
    ctypes.c_char: "Cchar",
    ctypes.c_size_t: "Csize_t",
    ctypes.c_ssize_t: "Cssize_t",
    # Pointers
    ctypes.c_char_p: "Ptr{Cchar}",
    ctypes.c_wchar_p: "Ptr{Cwchar_t}",
    ctypes.c_void_p: "Ptr{Cvoid}",
    ctypes.CDLL: "", # TODO: Temporary
}


FUNC_TYPE_MAP = {
    ctypes.cdll.LoadLibrary: lambda self, node, vargs: "ctypes.CDLL",
    ctypes.CDLL: lambda self, node, vargs: "ctypes.CDLL",
}
