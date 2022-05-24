import ast
import pickle
import getopt
import glob
from typing import BinaryIO, Callable, Dict, Tuple, Union
import zipfile

import pandas


class JuliaExternalModulePlugins:
    def visit_pycomm(t_self, node: ast.Call):
        JuliaExternalModulePlugins._pycall_import(t_self, node, "pythoncom")

    def visit_pywintypes(t_self, node: ast.Call):
        JuliaExternalModulePlugins._pycall_import(t_self, node, "pywintypes")

    def visit_datetime(t_self, node: ast.Call):
        # https://github.com/JuliaPy/PyCall.jl/issues/341
        JuliaExternalModulePlugins._pycall_import(t_self, node, "datetime")

    def visit_win32api(t_self, node: ast.Call):
        JuliaExternalModulePlugins._pycall_import(t_self, node, "win32api")

    def visit_win32ui(t_self, node):
        JuliaExternalModulePlugins._pycall_import(t_self, node, "win32ui")    

    def _pycall_import(t_self, node: ast.Call, mod_name: str):
        t_self._usings.add("PyCall")
        import_stmt = f"{mod_name} = pyimport(\"{mod_name}\")"
        t_self._globals.add(import_stmt)

    #######
    
    def visit_pandas_readcsv(t_self, node: ast.Call, vargs):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"read_csv({vargs[1]})"
    
    def visit_pandas_groupby(t_self, node: ast.Call, vargs):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"groupby({vargs[1]})"

    def visit_pandas_toexcel(t_self, node: ast.Call, vargs):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"to_excel({vargs[1]})"

    def visit_pandas_dataframe_sum(t_self, node: ast.Call, vargs):
        JuliaExternalModulePlugins._visit_pandas(t_self)
        return f"sum({vargs[0]})"

    def _visit_pandas(t_self):
        t_self._usings.add("Pandas")
    
    def visit_getopt(t_self, node: ast.Call, vargs):
        t_self._usings.add("Getopt")
        return f"getopt({', '.join(vargs)})"

    def visit_zipfile(t_self, node: ast.Call, vargs):
        t_self._usings.add("ZipFile")
        return f"ZipFile.Reader({vargs[0]})"

    def visit_glob(t_self, node, vargs):
        t_self._usings.add("Glob")
        return f"glob({vargs[0]})"

    def visit_picklestore(t_self, node, vargs):
        JuliaExternalModulePlugins._visit_pickle(t_self)
        return f"Pickle.store({vargs[0]})"

    def visit_pickleload(t_self, node, vargs):
        JuliaExternalModulePlugins._visit_pickle(t_self)
        return f"Pickle.load({vargs[0]})"

    def _visit_pickle(t_self):
        t_self._usings.add("Pickle")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    pandas.read_csv: (JuliaExternalModulePlugins.visit_pandas_readcsv, False),
    pandas.DataFrame.groupby: (JuliaExternalModulePlugins.visit_pandas_groupby, False),
    pandas.DataFrame.to_excel: (JuliaExternalModulePlugins.visit_pandas_toexcel, False),
    pandas.core.groupby.generic.DataFrameGroupBy.sum: (JuliaExternalModulePlugins.visit_pandas_dataframe_sum, False),
    # pickle
    pickle.Pickler: (JuliaExternalModulePlugins.visit_picklestore, False),
    pickle.Unpickler: (JuliaExternalModulePlugins.visit_pickleload, False),
    # Zipfile
    zipfile.ZipFile: (JuliaExternalModulePlugins.visit_zipfile, False),
    # Glob
    glob.glob: (JuliaExternalModulePlugins.visit_glob, False),
    # Getopt
    getopt.getopt: (JuliaExternalModulePlugins.visit_getopt, False), 
    # getopt.error: (lambda self, node, vargs: f"", False), # TODO: Nothing to support this
}


IMPORT_DISPATCH_TABLE = {
    "pythoncom": JuliaExternalModulePlugins.visit_pycomm,
    "pywintypes": JuliaExternalModulePlugins.visit_pywintypes,
    "datetime": JuliaExternalModulePlugins.visit_datetime,
    "win32api": JuliaExternalModulePlugins.visit_win32api,
    "win32ui": JuliaExternalModulePlugins.visit_win32ui,
}


IGNORED_MODULE_SET = set([
    "pythoncom",
    "pywintypes",
    "datetime",
    "pandas",
    "win32api",
    "win32ui",
])


EXTERNAL_TYPE_MAP = {
    BinaryIO: "IOBuffer"
}


