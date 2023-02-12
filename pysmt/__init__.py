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
        [
            "jgo",
            "--repository",
            "clojars.org=https://repo.clojars.org",
            "mvxcvi:cljstyle",
            *cljstyle_args,
        ],
        None,
        [],
        [infer_smt_types],
    )
