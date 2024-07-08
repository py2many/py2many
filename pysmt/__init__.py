import os

from py2many.language import LanguageSettings

from .inference import infer_smt_types
from .transpiler import SmtTranspiler


def settings(args, env=os.environ):
    return LanguageSettings(
        SmtTranspiler(),
        ".smt",
        "SMT",
        [
            "cljstyle",
            "fix",
        ],
        None,
        [],
        [infer_smt_types],
    )
