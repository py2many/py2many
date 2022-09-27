
import ast
from typing import Callable, Dict, Tuple, Union
try:
    import tqdm
except ImportError:
    tqdm = None

class JuliaExternalModulePlugins():
    def visit_tqdm(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("ProgressBars")
        # Using tqdm alias (Identical to using ProgressBar)
        return f"tqdm({', '.join(vargs)})"

if tqdm:
    FuncType = Union[Callable, str]

    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
        tqdm.tqdm: (JuliaExternalModulePlugins.visit_tqdm, True),
    }

IGNORED_MODULE_SET = set(["tqdm"])