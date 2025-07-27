import os

from py2many.language import LanguageSettings

from .inference import infer_smt_types
from .rewriters import AnnotatePreConditions, RewriteNotEq
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
        [AnnotatePreConditions(), RewriteNotEq()],
        [infer_smt_types],
    )
