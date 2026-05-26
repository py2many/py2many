import os
import shutil

from py2many.language import LanguageSettings

from .transpiler import DIntegerDivRewriter, DTranspiler


def _dfmt_command(dfmt_args):
    # `dub run dfmt` rebuilds/relinks dfmt on every call
    # (https://github.com/dlang-community/dfmt/issues/407) and dub can't build a
    # package safely from concurrent processes
    # (https://github.com/dlang/dub/issues/1113), so it races under pytest-xdist
    # with "Failed to execute ... dfmt (No such file or directory)". Prefer the
    # prebuilt binary on PATH (scripts/dlang-setup.sh builds it and .mise.toml
    # puts its dir on PATH); fall back to `dub run` only when it's absent.
    if shutil.which("dfmt"):
        return ["dfmt", *dfmt_args]
    return ["dub", "run", "--yes", "dfmt", "--", *dfmt_args]


def settings(args, env=os.environ):
    dfmt_args = ["--inplace", "--brace_style=otbs"]
    if args.indent is not None:
        dfmt_args.append(f"--indent_size={args.indent}")
    else:
        dfmt_args.append("--indent_size=2")
    return LanguageSettings(
        DTranspiler(),
        ".d",
        "D",
        _dfmt_command(dfmt_args),
        post_rewriters=[DIntegerDivRewriter()],
    )
