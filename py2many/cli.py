import argparse
import ast
import os
import pathlib

from dataclasses import dataclass
from typing import Optional

from .clike import CLikeTranspiler
from .scope import add_scope_context
from .annotation_transformer import add_annotation_flags
from .mutability_transformer import detect_mutable_vars
from .nesting_transformer import detect_nesting_levels
from .context import add_variable_context, add_list_calls
from .analysis import add_imports, is_void_function, get_id, is_mutable
from .inference import infer_types

from py14.transpiler import CppTranspiler
from pyrs.transpiler import RustTranspiler
from pyjl.transpiler import JuliaTranspiler
from pykt.transpiler import KotlinTranspiler
from pynim.transpiler import NimTranspiler
from pydart.transpiler import DartTranspiler
from pygo.transpiler import GoTranspiler


def transpile(source, transpiler):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    infer_meta = infer_types(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    add_imports(tree)

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
    formatter: str
    indent: Optional[int] = None


def cpp_settings(args):
    return LanguageSettings(CppTranspiler(), ".cpp", "clang-format -i")


def rust_settings(args):
    return LanguageSettings(RustTranspiler(), ".rs", "rustfmt")


def julia_settings(args):
    return LanguageSettings(JuliaTranspiler(), ".jl", "jlfmt")


def kotlin_settings(args):
    return LanguageSettings(KotlinTranspiler(), ".kt", "ktlint -F")


def nim_settings(args):
    nim_args = {}
    if args.indent is not None:
        nim_args["indent"] = args.indent
    return LanguageSettings(NimTranspiler(**nim_args), ".nim", "/bin/true")


def dart_settings(args):
    return LanguageSettings(DartTranspiler(), ".dart", "dart format")


def go_settings(args):
    return LanguageSettings(GoTranspiler(), ".go", "gofmt -w")


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
        print(f"Writing to: {outdir}")
        output_path = outdir / (source.stem + settings.ext)
        print(f"{filename}...{output_path}")
        with open(output_path, "w") as f:
            source_data = open(source).read()
            f.write(transpile(source_data, settings.transpiler))
        os.system(f"{settings.formatter} {output_path}")
        print()
