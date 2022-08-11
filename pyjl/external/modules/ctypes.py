import ast
import ctypes
import sys

from typing import Callable, Dict, Tuple, Union

from py2many.ast_helpers import get_id

class JuliaExternalModulePlugins():
    def visit_load_library(self, node, vargs):
        self._usings.add("Libdl")
        return f"Libdl.dlopen({vargs[0]})" if vargs else "Libdl.dlopen"

    def visit_cast(self, node, vargs):
        # (TODO) From Documentation: Neither convert nor cconvert should 
        # take a Julia object and turn it into a Ptr.
        self._usings.add("Libdl")
        return f"Base.cconvert({self._map_type(vargs[1])}, {vargs[0]})"

    def visit_cdata_value(self, node, vargs):
        # Remove the call to value (apparently, Julia already 
        # returns the value)
        if get_id(node.func) == "value":
            return self.visit(node.args[0])

    # Using Pycall
    def visit_pointer(self, node, vargs):
        # TODO: Change to ccall
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")
        # Unparse args to avoid mapping them to the corresponding Julia types
        args = []
        for arg in node.args:
            if (func := self._func_for_lookup(ast.unparse(arg))) != self._default_type:
                args.append(f"ctypes.{func.__name__}")
            else:
                args.append(ast.unparse(arg))
        return f"ctypes.POINTER({', '.join(args)})"

    def visit_create_unicode_buffer(self, node, vargs):
        # TODO: Change to ccall
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")

    def visit_pythonapi(self, node, vargs):
        # TODO: Search for DLL
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")
        return "ctypes.pythonapi"

    def visit_pyobject(self, node, vargs):
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")
        return f"ctypes.py_object({', '.join(vargs())})"
    
    def visit_winfunctype(self, node, vargs):
        # There is no equivalent call in Julia 
        JuliaExternalModulePlugins._pycall_import(self, node, "ctypes")
    
    def _pycall_import(self, node: ast.Call, mod_name: str):
        self._usings.add("PyCall")
        import_stmt = f'{mod_name} = pyimport("{mod_name}")'
        self._globals.add(import_stmt)

    # Windows-specific calls
    def visit_wintypes(self, node, vargs):
        self._usings.add("WinTypes")
        return f"WinTypes({', '.join(vargs)})"

    def visit_winerror(self, node, vargs):
        if len(vargs) == 5:
            parsed_args = f"{vargs[1]}, {vargs[4]}"
            return f"Base.windowserror({parsed_args})"
        return "Base.windowserror"


FuncType = Union[Callable, str]

GENERIC_DISPATCH_TABLE = {
    ctypes.cdll.LoadLibrary: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.CDLL: (JuliaExternalModulePlugins.visit_load_library, True),
    ctypes.cast: (JuliaExternalModulePlugins.visit_cast, True),
    ctypes._SimpleCData.value: (JuliaExternalModulePlugins.visit_cdata_value, True),
    ctypes.byref: (lambda self, node, vargs: f"pointer_from_objref({vargs[1]})" 
        if len(vargs) > 1 else "pointer_from_objref", True),
    ctypes.sizeof: (lambda self, node, vargs: f"sizeof({self._map_type(vargs[0])})" 
        if vargs else "sizeof", True),
    # Using PythonCall
    ctypes.POINTER: (JuliaExternalModulePlugins.visit_pointer, True),
    ctypes.pythonapi: (JuliaExternalModulePlugins.visit_pythonapi, True),
    ctypes.create_unicode_buffer: (JuliaExternalModulePlugins.visit_create_unicode_buffer, True),
    ctypes.py_object: (JuliaExternalModulePlugins.visit_pyobject, True)
}

GENERIC_SMALL_DISPATCH_MAP = {
    "ctypes.memset": lambda node, vargs: f"ccall(\"memset\", Ptr{{Cvoid}}, (Ptr{{Cvoid}}, Cint, Csize_t), {vargs[0]}, {vargs[1]}, {vargs[2]})",
    "pythonapi.PyBytes_FromStringAndSize": lambda node, vargs: "ctypes.pythonapi.PyBytes_FromStringAndSize",
}

if sys.platform.startswith('win32'):
    # Import windows ctypes modules
    from builtins import WindowsError
    from ctypes import wintypes

    WIN_SMALL_DISPATCH_MAP = {
        "GetLastError": lambda node, vargs: "Base.Libc.GetLastError",
        "ctypes.GetLastError": lambda node, vargs: "Base.Libc.GetLastError",
    }

    SMALL_DISPATCH_MAP = GENERIC_SMALL_DISPATCH_MAP | WIN_SMALL_DISPATCH_MAP

    WIN_DISPATCH_TABLE = {
        ctypes.WinDLL: (JuliaExternalModulePlugins.visit_load_library, True),
        # ctypes.GetLastError: (lambda self, node, vargs: "Base.Libc.GetLastError", True),
        ctypes.FormatError: (lambda self, node, vargs: f"Base.Libc.FormatMessage({', '.join(vargs)})", True),
        # wintypes
        wintypes: (JuliaExternalModulePlugins.visit_wintypes, True),
        ctypes.WINFUNCTYPE: (JuliaExternalModulePlugins.visit_winfunctype, True),
        # Exceptions
        WindowsError: (JuliaExternalModulePlugins.visit_winerror, True),
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
    ctypes.c_wchar_p: "Ptr{Cwchar_t}",
    ctypes.c_void_p: "Ptr{Cvoid}",
    ctypes.CDLL: "", # TODO: Temporary
    ctypes.py_object: "ctypes.py_object",
}


FUNC_TYPE_MAP = {
    ctypes.cdll.LoadLibrary: lambda self, node, vargs: "ctypes.CDLL",
    ctypes.CDLL: lambda self, node, vargs: "ctypes.CDLL",
    # Why invalid syntax???
    # ctypes.cast: lambda self, node, vargs: ast.unparse(vargs[1]) if vargs else "ctypes.cast",
    ctypes.cast: lambda self, node, vargs: "ctypes._SimpleCData",
}

IGNORED_MODULE_SET = set([
    "ctypes",
    "ctypes.wintypes"
])