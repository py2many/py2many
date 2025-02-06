import os

from py2many.language import LanguageSettings

from .inference import infer_zig_types
from .rewriters import ZigImplicitConstructor, ZigInferMoveSemantics
from .transpiler import ZigTranspiler


def settings(args, env=os.environ):
    zig_args = {}
    return LanguageSettings(
        ZigTranspiler(**zig_args),
        ".zig",
        "Zig",
        ["zig", "fmt"],
        None,
        [ZigInferMoveSemantics()],
        [infer_zig_types],
        post_rewriters=[
            ZigImplicitConstructor(),
        ],
    )
