import os

from py2many.language import LanguageSettings

from .inference import infer_mojo_types
from .rewriters import MojoImplicitConstructor, MojoInferMoveSemantics
from .transpiler import MojoTranspiler


def settings(args, env=os.environ):
    mojo_args = {}
    return LanguageSettings(
        MojoTranspiler(**mojo_args),
        ".mojo",
        "Mojo",
        ["mojo", "format"],
        None,
        [MojoInferMoveSemantics()],
        [infer_mojo_types],
        post_rewriters=[
            MojoImplicitConstructor(),
        ],
    )
