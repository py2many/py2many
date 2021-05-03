import argparse
import ast
import os
import pathlib
import subprocess

from dataclasses import dataclass, field
from distutils import spawn
from typing import Callable, List, Optional

from .analysis import add_imports
from .clike import CLikeTranspiler
from .scope import add_scope_context
from .annotation_transformer import add_annotation_flags
from .mutability_transformer import detect_mutable_vars
from .nesting_transformer import detect_nesting_levels
from .context import add_variable_context, add_list_calls
from .inference import infer_types

from py14.transpiler import CppTranspiler, CppListComparisonRewriter
from pyrs.inference import infer_rust_types
from pyrs.transpiler import (
    RustTranspiler,
    RustLoopIndexRewriter,
    RustNoneCompareRewriter,
)
from pyjl.transpiler import JuliaTranspiler, JuliaMethodCallRewriter
from pykt.inference import infer_kotlin_types
from pykt.transpiler import KotlinTranspiler, KotlinPrintRewriter
from pynim.inference import infer_nim_types
from pynim.transpiler import NimTranspiler, NimNoneCompareRewriter
from pydart.transpiler import DartTranspiler
from pygo.inference import infer_go_types
from pygo.transpiler import (
    GoTranspiler,
    GoMethodCallRewriter,
    GoNoneCompareRewriter,
    GoPropagateTypeAnnotation,
)

from py2many.rewriters import ComplexDestructuringRewriter, PythonMainRewriter


def transpile(source, transpiler, rewriters, transformers, post_rewriters):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    language = transpiler.NAME
    generic_rewriters = [
        ComplexDestructuringRewriter(language),
        PythonMainRewriter(language),
    ]

    # This is very basic and needs to be run before and after
    # rewrites. Revisit if running it twice becomes a perf issue
    add_scope_context(tree)
    # First run Language independent rewriters
    for rewriter in generic_rewriters:
        tree = rewriter.visit(tree)
    # Language specific rewriters
    for rewriter in rewriters:
        tree = rewriter.visit(tree)
    # Language independent transformers
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    infer_meta = infer_types(tree)
    add_imports(tree)
    # Language specific transformers
    for tx in transformers:
        tx(tree)
    # Language specific rewriters that depend on previous steps
    for rewriter in post_rewriters:
        tree = rewriter.visit(tree)

    out = []
    code = transpiler.visit(tree) + "\n"
    headers = transpiler.headers(infer_meta)
    if headers:
        out.append(headers)
    usings = transpiler.usings()
    if usings:
        out.append(usings)
    out.append(code)
    return "\n".join(out)


@dataclass
class LanguageSettings:
    transpiler: CLikeTranspiler
    ext: str
    formatter: Optional[List[str]] = None
    indent: Optional[int] = None
    rewriters: List[ast.NodeVisitor] = field(default_factory=list)
    transformers: List[Callable] = field(default_factory=list)
    post_rewriters: List[ast.NodeVisitor] = field(default_factory=list)


def cpp_settings(args):
    return LanguageSettings(
        CppTranspiler(),
        ".cpp",
        ["clang-format", "-i"],
        None,
        [CppListComparisonRewriter()],
    )


def rust_settings(args):
    return LanguageSettings(
        RustTranspiler(),
        ".rs",
        ["rustfmt"],
        None,
        [RustNoneCompareRewriter()],
        [infer_rust_types],
        [RustLoopIndexRewriter()],
    )


def julia_settings(args):
    format_jl = spawn.find_executable("format.jl")
    if format_jl:
        format_jl = ["julia", "-O0", "--compile=min", "--startup=no", format_jl]
    else:
        format_jl = ["format.jl"]
    return LanguageSettings(
        JuliaTranspiler(), ".jl", format_jl, None, [], [], [JuliaMethodCallRewriter()]
    )


def kotlin_settings(args):
    return LanguageSettings(
        KotlinTranspiler(),
        ".kt",
        ["ktlint", "-F"],
        None,
        [KotlinPrintRewriter()],
        [infer_kotlin_types],
    )


def nim_settings(args):
    nim_args = {}
    nimpretty_args = []
    if args.indent is not None:
        nim_args["indent"] = args.indent
        nimpretty_args.append(f"--indent:{args.indent}")
    return LanguageSettings(
        NimTranspiler(**nim_args),
        ".nim",
        ["nimpretty", *nimpretty_args],
        None,
        [NimNoneCompareRewriter()],
        [infer_nim_types],
    )


def dart_settings(args):
    return LanguageSettings(DartTranspiler(), ".dart", ["dart", "format"])


def go_settings(args):
    return LanguageSettings(
        GoTranspiler(),
        ".go",
        ["gofmt", "-w"],
        None,
        [GoNoneCompareRewriter()],
        [infer_go_types],
        [GoMethodCallRewriter(), GoPropagateTypeAnnotation()],
    )


def _get_all_settings(args):
    return {
        "cpp": cpp_settings(args),
        "rust": rust_settings(args),
        "julia": julia_settings(args),
        "kotlin": kotlin_settings(args),
        "nim": nim_settings(args),
        "dart": dart_settings(args),
        "go": go_settings(args),
    }


def _process_once(settings, filename, outdir):
    """Transpile and reformat.

    Returns False if reformatter failed.
    """
    output_path = outdir / (filename.stem + settings.ext)
    if settings.ext == ".kt" and output_path.is_absolute():
        # KtLint does not support absolute path in globs
        output_path = output_path.relative_to(pathlib.Path.cwd())
    print(f"{filename}...{output_path}")
    with open(filename) as f:
        source_data = f.read()
    with open(output_path, "w") as f:
        f.write(
            transpile(
                source_data,
                settings.transpiler,
                settings.rewriters,
                settings.transformers,
                settings.post_rewriters,
            )
        )
    if settings.formatter:
        if subprocess.call([*settings.formatter, output_path]):
            print(f"Error: Could not reformat: {output_path}")
            return False
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpp", type=bool, default=False, help="Generate C++ code")
    parser.add_argument("--rust", type=bool, default=False, help="Generate Rust code")
    parser.add_argument("--julia", type=bool, default=False, help="Generate Julia code")
    parser.add_argument(
        "--kotlin", type=bool, default=False, help="Generate Kotlin code"
    )
    parser.add_argument("--nim", type=bool, default=False, help="Generate Nim code")
    parser.add_argument("--dart", type=bool, default=False, help="Generate Dart code")
    parser.add_argument("--go", type=bool, default=False, help="Generate Go code")
    parser.add_argument("--outdir", default=None, help="Output directory")
    parser.add_argument(
        "-i",
        "--indent",
        type=int,
        default=None,
        help="Indentation to use in languages that care",
    )
    args, rest = parser.parse_known_args()
    for filename in rest:
        settings = cpp_settings(args)
        if args.cpp:
            pass
        if args.rust:
            settings = rust_settings(args)
        elif args.julia:
            settings = julia_settings(args)
        elif args.kotlin:
            settings = kotlin_settings(args)
        elif args.nim:
            settings = nim_settings(args)
        elif args.dart:
            settings = dart_settings(args)
        elif args.go:
            settings = go_settings(args)
        source = pathlib.Path(filename)
        if args.outdir is None:
            outdir = source.parent
        else:
            outdir = pathlib.Path(args.outdir)

        if source.is_file():
            print(f"Writing to: {outdir}")
            _process_once(settings, source, outdir)
        else:
            if args.outdir is None:
                outdir = source.parent / f"{source.name}-py2many"

            print(f"Transpiling whole directiory to {outdir}:")
            successful = failures = format_errors = 0
            for path in source.rglob("*.py"):
                if path.suffix != ".py":
                    continue
                if path.parent.name == "__pycache__":
                    continue

                relative_path = path.relative_to(source)
                target_path = outdir / relative_path
                target_dir = target_path.parent
                os.makedirs(target_dir, exist_ok=True)

                try:
                    if _process_once(settings, path, target_dir):
                        print(f"Error: Could not reformat: {path}")
                        format_errors += 1
                    successful += 1
                except Exception as e:
                    failures += 1
                    print(f"Error: Could not transpile: {path}")
                    print(f"Due to: {e}")

            print("\nFinished!")
            print(f"Successful: {successful}")
            if format_errors:
                print(f"Failed to reformat: {format_errors}")
            print(f"Failed to convert: {failures}")
            print()
