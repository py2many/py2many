import os

from py2many.language import LanguageSettings

from .inference import infer_nim_types
from .transpiler import NimNoneCompareRewriter, NimTranspiler


def settings(args, env=os.environ):
    nim_args = {}
    nimpretty_args = []
    if args.indent is not None:
        nim_args["indent"] = args.indent
        nimpretty_args.append(f"--indent:{args.indent}")
    return LanguageSettings(
        NimTranspiler(**nim_args),
        ".nim",
        "Nim",
        ["nimpretty", *nimpretty_args],
        None,
        [NimNoneCompareRewriter()],
        [infer_nim_types],
    )
