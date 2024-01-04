import os
from functools import lru_cache
from pathlib import Path
from subprocess import run

from py2many.language import LanguageSettings
from py2many.process_helpers import find_executable

from .inference import infer_julia_types
from .rewriters import JuliaBoolOpRewriter, JuliaIndexingRewriter
from .transpiler import JuliaMethodCallRewriter, JuliaTranspiler


@lru_cache()
def _julia_formatter_path():
    proc = run(
        ["julia", "-e", "import JuliaFormatter;print(pathof(JuliaFormatter))"],
        capture_output=True,
    )
    if not proc.returncode and proc.stdout:
        return str(Path(proc.stdout.decode("utf8")).parent.parent / "bin" / "format.jl")


def settings(args, env=os.environ):
    format_jl = find_executable("format.jl")
    if not format_jl:
        julia = find_executable("julia")
        if julia:
            format_jl = _julia_formatter_path()

    if format_jl:
        format_jl = ["julia", "-O0", "--compile=min", "--startup=no", format_jl, "-v"]
    else:
        format_jl = ["format.jl", "-v"]
    return LanguageSettings(
        JuliaTranspiler(),
        ".jl",
        "Julia",
        format_jl,
        None,
        rewriters=[],
        transformers=[infer_julia_types],
        post_rewriters=[
            JuliaIndexingRewriter(),
            JuliaMethodCallRewriter(),
            JuliaBoolOpRewriter(),
        ],
    )
