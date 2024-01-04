import os
from functools import partial

from py2many.language import LanguageSettings

from .inference import infer_rust_types
from .transpiler import (
    RustLoopIndexRewriter,
    RustNoneCompareRewriter,
    RustStringJoinRewriter,
    RustTranspiler,
)


def settings(args, env=os.environ):
    return LanguageSettings(
        RustTranspiler(args.extension, args.no_prologue),
        ".rs",
        "Rust",
        [
            "rustup",
            "run",
            "nightly",
            "rustfmt",
            "--edition=2021",
        ],
        None,
        [RustNoneCompareRewriter()],
        [partial(infer_rust_types, extension=args.extension)],
        [RustLoopIndexRewriter(), RustStringJoinRewriter()],
        linter=[
            "rustup",
            "run",
            "nightly",
            "cargo",
            "clippy",
            "-Zscript",
            "--manifest-path",
        ],
    )
