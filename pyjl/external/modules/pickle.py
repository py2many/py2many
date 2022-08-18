import ast
import pickle
from typing import Callable, Dict, Tuple, Union


class JuliaExternalModulePlugins:
    def visit_picklestore(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pickle(t_self)
        return f"Pickle.store({vargs[0]})"

    def visit_pickleload(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pickle(t_self)
        parsed_args = []
        keywords = []
        call = "Pickle.load"
        if getattr(node, "type_comment", None) == "numpy":
            call = "Pickle.npyload"
        for arg in node.args:
            parsed_args.append(t_self.visit(arg))
        for kwarg in node.keywords:
            if kwarg.arg == "":
                pass
            keywords.append(t_self.visit(kwarg))
        return f"{call}({', '.join(parsed_args)})"

    def visit_pickledump(t_self, node: ast.Call, vargs: list[str]):
        JuliaExternalModulePlugins._visit_pickle(t_self)
        return f"Pickle.dump({vargs[0]})"

    def _visit_pickle(t_self):
        t_self._usings.add("Pickle")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # pickle
    pickle.load: (JuliaExternalModulePlugins.visit_pickleload, False),
    pickle.Pickler: (JuliaExternalModulePlugins.visit_picklestore, False),
    pickle.Unpickler: (JuliaExternalModulePlugins.visit_pickleload, False),
    pickle.Pickler.dump: (JuliaExternalModulePlugins.visit_pickledump, False),
}

FUNC_TYPE_MAP = {pickle.Pickler: lambda self, node, vargs, kwargs: "pickle.Pickler"}
