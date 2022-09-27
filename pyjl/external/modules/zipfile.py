import ast
from typing import Callable, Dict, Tuple, Union
try:
    import zipfile
except ImportError:
    zipfile = None

class JuliaExternalModulePlugins:
    def visit_zipfile(t_self, node: ast.Call, vargs: list[str]):
        t_self._usings.add("ZipFile")
        return f"ZipFile.Reader({vargs[0]})"

if zipfile:
    FuncType = Union[Callable, str]

    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
        zipfile.ZipFile: (JuliaExternalModulePlugins.visit_zipfile, False),
    }