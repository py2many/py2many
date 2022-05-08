import ast
from ctypes import Union
from typing import Callable, Dict, List, Tuple

# TODO: Module name should change from "plugins" to something more indicative

##################################
## Plugins

class JuliaExternalTranspilerPlugins:
    def visit_pycomm(t_self, node: ast.Call, vargs: List[str]):
        t_self._usings.add("PyCall")
        import_stmt = "pythoncom = pyimport(\"pythoncom\")"
        t_self._globals.add(import_stmt)
        return "pythoncom"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "pythoncom._GetInterfaceCount": "pythoncom._GetInterfaceCount"
}


MODULE_DISPATCH_TABLE: Dict[str, str] = {
    # TODO: This is somewhat of a hack
    "pythoncom": JuliaExternalTranspilerPlugins.visit_pycomm,
}


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
}
