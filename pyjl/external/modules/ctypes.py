import ast
import subprocess
import ctypes
from ctypes import wintypes
import os
import sys

from typing import Callable, Dict, Optional, Tuple, Union

from py2many.ast_helpers import get_id

class JuliaExternalModulePlugins():
    def visit_load_library(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("Libdl")
        return f"Libdl.dlopen({vargs[0]})" if vargs else "Libdl.dlopen"

    def visit_pythonapi(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("Libdl")
        # Checks the path of the dll for Python 3.9
        python_39_path = subprocess.check_output('where python39.dll').decode().strip()
        python_39 = f"\"{'/'.join(python_39_path.split(os.sep))}\""
        self._globals.add(f"pythonapi = Libdl.dlopen({python_39})")
        func = self.visit(node.func)
        if getattr(node, "in_ccall", None):
            return f"Libdl.dlsym(pythonapi, :{func})"
        elif getattr(node, "is_attr", None):
            return f"(argtypes, return_type, args) -> @ccall (Libdl.dlsym(pythonapi, :{func}), return_type, argtypes, args)"
        return f"ccall({', '.join(vargs)})"
  
    # def visit_pythonapi(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
    #     # TODO: Search for DLL
    #     JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")
    #     return f"ctypes.pythonapi.{self.visit(node.func)}"

    def visit_cast(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        # (TODO) From Documentation: Neither convert nor cconvert should 
        # take a Julia object and turn it into a Ptr.
        self._usings.add("Libdl")
        return f"convert({self._map_type(vargs[1])}, {vargs[0]})"

    def visit_cdata_value(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        # Remove the call to value (apparently, Julia already 
        # returns the value)
        if get_id(node.func) == "value":
            return self.visit(node.args[0])

    def visit_byref(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        if getattr(node, "is_attr", None):
            return "x -> pointer_from_objref(x)"
        if len(vargs) > 0:
            return f"pointer_from_objref({vargs[0]})"
        return "pointer_from_objref"

    def visit_pointer(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        return f"pointer_from_objref({vargs[0]})"
    
    # Using Pycall
    def visit_create_unicode_buffer(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        # TODO: Change to ccall
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")

    def _pycall_import(self, node: ast.Call, mod_name: str, opt_name: Optional[str] = None):
        self._usings.add("PyCall")
        if opt_name:
            import_stmt = f'{opt_name} = pyimport("{mod_name}")'
        else:
            import_stmt = f'{mod_name} = pyimport("{mod_name}")'
        self._globals.add(import_stmt)

    # Windows-specific calls
    def visit_wintypes(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("WinTypes")
        return f"WinTypes({', '.join(vargs)})"

    # Hacks
    def visit_Libdl(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
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
    "ccall": JuliaExternalModulePlugins.visit_Libdl # Small hack to import Libdl
}

GENERIC_SMALL_DISPATCH_MAP = {
    "ctypes.memset": lambda node, vargs, kwargs: f"ccall(\"memset\", Ptr{{Cvoid}}, (Ptr{{Cvoid}}, Cint, Csize_t), {vargs[0]}, {vargs[1]}, {vargs[2]})",
    "LPCWSTR": lambda node, vargs, kwargs: f"convert(Cwstring, {', '.join(vargs)})" #TODO: Review
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
    ctypes.c_longlong: "Clonglong", # Is recognized as ctypes.c_ssize_t
    ctypes.c_ulonglong: "Culonglong",
    # ctypes.c_longdouble: "", # No mapping
    ctypes.c_byte: "Cuint", # TODO: Check this
    ctypes.c_ubyte: "Cuint", # TODO: Check this
    ctypes.c_char: "Cchar",
    ctypes.c_size_t: "Csize_t",
    ctypes.c_ssize_t: "Cssize_t",
    ctypes.c_wchar: "Cwchar_t",
    # Pointers
    ctypes.c_char_p: "Ptr{Cchar}",
    ctypes.c_wchar_p: "Cwstring",
    ctypes.c_void_p: "Ptr{Cvoid}",
    ctypes.CDLL: "", # TODO: Temporary
    ctypes.WinDLL: "",
    ctypes.py_object: "Ptr{Cvoid}",
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
