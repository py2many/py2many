import shutil
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    shutil.rmtree: (lambda self, node, vargs: f"Base.Filesystem.rm({vargs[0]}, recursive=True)", True),
    shutil.copy: (lambda self, node, vargs: f"Base.Filesystem.cp({vargs[0]}, {vargs[1]}, follow_symlinks={vargs[2]})"
        if len(vargs) == 3 else f"Base.Filesystem.cp({vargs[0]}, {vargs[1]})", True),
    shutil.move: (lambda self, node, vargs: f"Base.Filesystem.mv({vargs[0]}, {vargs[1]})", True),
    shutil.chown: (lambda self, node, vargs: f"Base.Filesystem.chown({vargs[0]}, {vargs[1]}, {vargs[2]})"
        if len(vargs) == 3 else "Base.Filesystem.chown", True),
}

IGNORED_MODULE_SET = set([
    "shutil"
])