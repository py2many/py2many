import os

from py2many.language import LanguageSettings

from .inference import infer_lean_types
from .rewriters import LeanImplicitConstructor
from .transpiler import LeanTranspiler

_LEAN_FMT = os.path.join(os.path.dirname(__file__), "fmt.lean")


def settings(args, env=os.environ):
    return LanguageSettings(
        LeanTranspiler(),
        ".lean",
        "Lean",
        # No standalone Lean source formatter exists yet, so drive the compiler's
        # own pretty printer (Lean.PrettyPrinter.ppModule) via fmt.lean, which
        # rewrites the file in place. _create_cmd appends the output path.
        formatter=["lean", "--run", _LEAN_FMT],
        rewriters=[],
        transformers=[infer_lean_types],
        post_rewriters=[LeanImplicitConstructor()],
    )
