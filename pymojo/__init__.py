import os

from py2many.language import LanguageSettings

from .inference import infer_mojo_types
from .transpiler import MojoNoneCompareRewriter, MojoTranspiler


def settings(args, env=os.environ):
    mojo_args = {}
    mojopretty_args = []
    if args.indent is not None:
        mojo_args["indent"] = args.indent
        mojopretty_args.append(f"--indent:{args.indent}")
    return LanguageSettings(
        MojoTranspiler(**mojo_args),
        ".mojo",
        "Mojo",
        ["mojopretty", *mojopretty_args],
        None,
        [MojoNoneCompareRewriter()],
        [infer_mojo_types],
    )
