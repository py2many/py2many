import ast
import subprocess
import ctypes
from ctypes import wintypes
import os
import sys

from typing import Callable, Dict, Optional, Tuple, Union

from py2many.ast_helpers import get_id
from pyjl.helpers import pycall_import

class JuliaExternalModulePlugins():
    def visit_load_library(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Libdl")
        return f"Libdl.dlopen({vargs[0]})" if vargs else "Libdl.dlopen"

    def visit_pythonapi(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Libdl")
        # Get path of the dll for Python 3.9
        python_39 = JuliaExternalModulePlugins._get_python_dll_path((3, 9))
        self._globals.add(f"pythonapi = Libdl.dlopen({python_39})")
        func = self.visit(node.func)
        if getattr(node, "in_ccall", None):
            return f"Libdl.dlsym(pythonapi, :{func})"
        elif getattr(node, "is_attr", None):
            return f"(argtypes, return_type, args) -> @ccall (Libdl.dlsym(pythonapi, :{func}), return_type, argtypes, args)"
        return f"ccall({', '.join(vargs)})"

    def _get_python_dll_path(version: tuple[str, str]):
        """Receives major and minor version information 
        and returns the corresponding Python DLL path"""
        if len(version) != 2:
            return None
        # Checks the path of the dll for Python 
        # given a version number
        version_str = f"{version[0]}{version[1]}"
        python_path = subprocess.check_output(f'where python{version_str}.dll').decode().strip().split("\n")
        python_path = python_path[1] \
            if len(python_path) > 1 \
            else python_path[0]
        return f"\"{'/'.join(python_path.strip().split(os.sep))}\""

    def visit_cast(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Libdl")
        return f"Base.cconvert({self._map_type(vargs[1])}, {vargs[0]})"

    def visit_cdata_value(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        # Remove the call to value (apparently, Julia already 
        # returns the value)
        conversion_type = None
        if isinstance(node.args[0], ast.Call) and \
                get_id(node.args[0].func) == "ctypes.cast":
            conversion_type = get_id(node.args[0].args[1])
        if conversion_type == "LPCWSTR":
            return f"unsafe_string({vargs[0]})"
        return f"unsafe_load({vargs[0]})"

    def visit_byref(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        if getattr(node, "is_attr", None):
            return "x -> pointer_from_objref(x)"
        if len(vargs) > 0:
            return f"pointer_from_objref({vargs[0]})"
        return "pointer_from_objref"

    def visit_pointer(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        return f"pointer_from_objref({vargs[0]})"
    
    # Using Pycall
    def visit_create_unicode_buffer(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        # TODO: Change to ccall
        pycall_import(self, node, "ctypes")

    # Windows-specific calls
    def visit_wintypes(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("WinTypes")
        return f"WinTypes({', '.join(vargs)})"

    # Hacks
    def visit_Libdl(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Libdl")


FuncType = Union[Callable, str]

GENERIC_DISPATCH_TABLE = {
    ctypes.cdll.LoadLibrary: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.CDLL: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.PyDLL: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.pythonapi: (JuliaExternalModulePlugins.visit_pythonapi, True), # Not working
    ctypes.cast: (JuliaExternalModulePlugins.visit_cast, True),
    ctypes._SimpleCData.value: (JuliaExternalModulePlugins.visit_cdata_value, True),
    ctypes.byref: (JuliaExternalModulePlugins.visit_byref, True),
    ctypes.sizeof: (lambda self, node, vargs, kwargs: f"sizeof({self._map_type(vargs[0])})" 
        if vargs else "sizeof", True),
    # Using PythonCall
    ctypes.POINTER: (JuliaExternalModulePlugins.visit_pointer, True),
    ctypes.create_unicode_buffer: (JuliaExternalModulePlugins.visit_create_unicode_buffer, True),
}

DISPATCH_MAP = {
    "pythonapi.PyBytes_FromStringAndSize": JuliaExternalModulePlugins.visit_pythonapi,
    "ccall": JuliaExternalModulePlugins.visit_Libdl, # Small hack to import Libdl
}

GENERIC_SMALL_DISPATCH_MAP = {
    "ctypes.memset": lambda node, vargs, kwargs: f"ccall(\"memset\", Ptr{{Cvoid}}, (Ptr{{Cvoid}}, Cint, Csize_t), {vargs[0]}, {vargs[1]}, {vargs[2]})",
    "LPCWSTR": lambda node, vargs, kwargs: f"isa({vargs[0]}, String) ? Cwstring(pointer(transcode(Cwchar_t, {vargs[0]}))) : Cwstring(Ptr{{Cwchar_t}}({vargs[0]}))"
}

if sys.platform.startswith('win32'):
    # Import windows ctypes modules
    from builtins import WindowsError
    from ctypes import wintypes

    WIN_SMALL_DISPATCH_MAP = {
        "GetLastError": lambda node, vargs, kwargs: "Base.Libc.GetLastError" 
            if getattr(node, "is_attr", None)
            else "Base.Libc.GetLastError()",
        "ctypes.GetLastError": lambda node, vargs, kwargs: "Base.Libc.GetLastError" 
            if getattr(node, "is_attr", None)
            else "Base.Libc.GetLastError()",
    }

    SMALL_DISPATCH_MAP = GENERIC_SMALL_DISPATCH_MAP | WIN_SMALL_DISPATCH_MAP

    WIN_DISPATCH_TABLE = {
        ctypes.WinDLL: (JuliaExternalModulePlugins.visit_load_library, True),
        ctypes.windll.LoadLibrary: (JuliaExternalModulePlugins.visit_load_library, True),
        # ctypes.WinDLL: (JuliaExternalModulePlugins.visit_windll, True),
        # ctypes.GetLastError: (lambda self, node, vargs, kwargs: "Base.Libc.GetLastError", True),
        ctypes.FormatError: (lambda self, node, vargs, kwargs: f"Base.Libc.FormatMessage({', '.join(vargs)})", True),
        wintypes: (JuliaExternalModulePlugins.visit_wintypes, True),
    }
    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = GENERIC_DISPATCH_TABLE | WIN_DISPATCH_TABLE
else:
    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = GENERIC_DISPATCH_TABLE


EXTERNAL_TYPE_MAP = {
    ctypes.c_int: lambda self: "Cint",
    ctypes.c_int8: lambda self: "Cint",
    ctypes.c_int16: lambda self: "Cint",
    ctypes.c_int32: lambda self: "Cint",
    ctypes.c_int64: lambda self: "Cint",
    ctypes.c_uint8: lambda self: "Cuint",
    ctypes.c_uint16: lambda self: "Cuint",
    ctypes.c_uint32: lambda self: "Cuint",
    ctypes.c_uint64: lambda self: "Cuint",
    ctypes.c_bool: lambda self: "Cbool",
    ctypes.c_float: lambda self: "Cfloat",
    ctypes.c_double: lambda self: "Cdouble",
    ctypes.c_short: lambda self: "Cshort",
    ctypes.c_ushort: lambda self: "Cushort",
    ctypes.c_long: lambda self: "Clong",
    ctypes.c_ulong: lambda self: "Culong",
    ctypes.c_longlong: lambda self: "Clonglong", # Is recognized as ctypes.c_ssize_t
    ctypes.c_ulonglong: lambda self: "Culonglong",
    # ctypes.c_longdouble: "", # No mapping
    ctypes.c_byte: lambda self: "Cuint", # TODO: Check this
    ctypes.c_ubyte: lambda self: "Cuint", # TODO: Check this
    ctypes.c_char: lambda self: "Cchar",
    ctypes.c_size_t: lambda self: "Csize_t",
    ctypes.c_ssize_t: lambda self: "Cssize_t",
    ctypes.c_wchar: lambda self: "Cwchar_t",
    # Pointers
    ctypes.c_char_p: lambda self: "Ptr{Cchar}",
    ctypes.c_wchar_p: lambda self: "Cwstring", # Ptr{Cwchar_t}
    ctypes.c_void_p: lambda self: "Ptr{Cvoid}",
    ctypes.CDLL: lambda self: "", # TODO: Temporary
    ctypes.WinDLL: lambda self: "",
    ctypes.py_object: lambda self: "Ptr{Cvoid}",
}


FUNC_TYPE_MAP = {
    ctypes.cdll.LoadLibrary: lambda self, node, vargs, kwargs: "ctypes.CDLL",
    ctypes.windll.LoadLibrary: lambda self, node, vargs, kwargs: "ctypes.WinDLL",
    ctypes.CDLL: lambda self, node, vargs, kwargs: "ctypes.CDLL",
    ctypes.WinDLL: lambda self, node, vargs, kwargs: "ctypes.WinDLL",
    ctypes.PyDLL: lambda self, node, vargs, kwargs: "ctypes.CDLL", # Hack, for now
    # Why invalid syntax???
    # ctypes.cast: lambda self, node, vargs, kwargs: ast.unparse(vargs[1]) if vargs else "ctypes.cast",
    ctypes.cast: lambda self, node, vargs, kwargs: "ctypes._SimpleCData",
    ctypes.WINFUNCTYPE: lambda self, node, vargs, kwargs: "PyObject",
    ctypes.POINTER: lambda self, node, vargs, kwargs: "ctypes.POINTER",
    WindowsError: lambda self, node, vargs, kwargs: "OSError",
}

IGNORED_MODULE_SET = set([
    "ctypes",
    "ctypes.wintypes"
])
