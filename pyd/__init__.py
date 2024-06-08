import os

from py2many.language import LanguageSettings

from .transpiler import DartIntegerDivRewriter, DartTranspiler


def settings(args, env=os.environ):
    return LanguageSettings(
        DartTranspiler(),
        ".dart",
        "Dart",
        ["dart", "format"],
        post_rewriters=[DartIntegerDivRewriter()],
    )
