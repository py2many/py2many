import os

from py2many.language import LanguageSettings

from .transpiler import DIntegerDivRewriter, DTranspiler


def settings(args, env=os.environ):
    return LanguageSettings(
        DTranspiler(),
        ".d",
        "D",
        [
            "dub",
            "run",
            "--yes",
            "dfmt",
            "--",
            "--inplace",
            "--brace_style=otbs",
            "--indent_size=2",
        ],
        post_rewriters=[DIntegerDivRewriter()],
    )
