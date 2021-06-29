import os

from py2many.language import LanguageSettings

from .inference import infer_v_types
from .transpiler import (
    VComprehensionRewriter,
    VDictRewriter,
    VNoneCompareRewriter,
    VTranspiler,
)


def settings(args, env=os.environ):
    v_args = {}
    vfmt_args = ["fmt", "-w"]
    if args.indent is not None:
        v_args["indent"] = args.indent
        vfmt_args.append(f"--indent:{args.indent}")
    return LanguageSettings(
        VTranspiler(**v_args),
        ".v",
        "V",
        ["v", *vfmt_args],
        None,
        [VNoneCompareRewriter(), VDictRewriter(), VComprehensionRewriter()],
        [infer_v_types],
    )
