from typing import Callable, Dict, Tuple, Union
import multiprocessing


class JuliaExternalModulePlugins:
    def visit_starmap(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_distributed_visit(t_self)
        return f"pmap({vargs[1]}, {vargs[2]})"

    def visit_Pool(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_distributed_visit(t_self)
        return "default_worker_pool()"

    def visit_map(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_distributed_visit(t_self)
        return f"pmap({vargs[1]}, {vargs[2]})"

    def _generic_distributed_visit(t_self):
        t_self._usings.add("Distributed")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    multiprocessing.cpu_count: (
        lambda self, node, vargs: f"length(Sys.cpu_info())",
        True,
    ),
    multiprocessing.Pool: (JuliaExternalModulePlugins.visit_Pool, True),
    "starmap": (
        JuliaExternalModulePlugins.visit_starmap,
        True,
    ),  # TODO: remove string-based fallback
}
