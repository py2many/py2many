import os

from py2many.language import LanguageSettings

from .inference import infer_lean_types
from .rewriters import LeanImplicitConstructor
from .transpiler import LeanTranspiler


def settings(args, env=os.environ):
    return LanguageSettings(
        LeanTranspiler(),
        ".lean",
        "Lean",
        # No widely-available standalone Lean source formatter, so leave the
        # generated output as emitted.
        formatter=None,
        rewriters=[],
        transformers=[infer_lean_types],
        post_rewriters=[LeanImplicitConstructor()],
    )
