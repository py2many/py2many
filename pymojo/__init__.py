import os

from py2many.language import LanguageSettings

from .inference import infer_mojo_types
from .transpiler import MojoNoneCompareRewriter, MojoTranspiler


def settings(args, env=os.environ):
    mojo_args = {}
    return LanguageSettings(
        MojoTranspiler(**mojo_args),
        ".mojo",
        "Mojo",
        ["mojo", "format"],
        None,
        [MojoNoneCompareRewriter()],
        [infer_mojo_types],
    )
