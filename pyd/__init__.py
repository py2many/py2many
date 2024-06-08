import os

from py2many.language import LanguageSettings

from .transpiler import DIntegerDivRewriter, DTranspiler


def settings(args, env=os.environ):
    return LanguageSettings(
        DTranspiler(),
        ".d",
        "D",
        ["d", "format"],
        post_rewriters=[DIntegerDivRewriter()],
    )
