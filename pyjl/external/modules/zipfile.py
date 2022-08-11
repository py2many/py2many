import ast
import zipfile

from typing import Callable, Dict, Tuple, Union

class JuliaExternalModulePlugins:
    def visit_zipfile(t_self, node: ast.Call, vargs: list[str]):
        t_self._usings.add("ZipFile")
        return f"ZipFile.Reader({vargs[0]})"

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    zipfile.ZipFile: (JuliaExternalModulePlugins.visit_zipfile, False),
}