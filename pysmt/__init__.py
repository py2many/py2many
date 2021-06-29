import os

from py2many.language import LanguageSettings

from .inference import infer_smt_types
from .transpiler import SmtTranspiler


def settings(args, env=os.environ):
    cljstyle_args = ["fix"]
    return LanguageSettings(
        SmtTranspiler(),
        ".smt",
        "SMT",
        ["cljstyle", *cljstyle_args],
        None,
        [],
        [infer_smt_types],
    )
