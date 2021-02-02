#!/usr/bin/env python3

import argparse
import ast
import os
import pathlib

from common.clike import CLikeTranspiler
from common.scope import add_scope_context
from common.annotation_transformer import add_annotation_flags
from common.mutability_transformer import detect_mutable_vars
from common.nesting_transformer import detect_nesting_levels
from common.context import add_variable_context, add_list_calls
from common.analysis import add_imports, is_void_function, get_id, is_mutable
from common.inference import infer_types
from dataclasses import dataclass

from py14.transpiler import CppTranspiler
from pyrs.transpiler import RustTranspiler
from pyjl.transpiler import JuliaTranspiler
from pykt.transpiler import KotlinTranspiler
from pynim.transpiler import NimTranspiler
from pydart.transpiler import DartTranspiler


def transpile(source, transpiler):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    infer_types(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    add_imports(tree)

    out = []
    code = transpiler.visit(tree) + "\n"
    headers = transpiler.headers()
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


def cpp_settings():
    return LanguageSettings(CppTranspiler(), ".cpp", "clang-format -i")


def rust_settings():
    return LanguageSettings(RustTranspiler(), ".rs", "rustfmt")


def julia_settings():
    return LanguageSettings(JuliaTranspiler(), ".jl", "jlfmt")


def kotlin_settings():
    return LanguageSettings(KotlinTranspiler(), ".kt", "ktlint -F")


def nim_settings():
    return LanguageSettings(NimTranspiler(), ".nim", "/bin/true")


def dart_settings():
    return LanguageSettings(DartTranspiler(), ".dart", "dart format")


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
    parser.add_argument("--outdir", default=None, help="Output directory")
    args, rest = parser.parse_known_args()
    for filename in rest:
        settings = cpp_settings()
        if args.cpp:
            pass
        if args.rust:
            settings = rust_settings()
        elif args.julia:
            settings = julia_settings()
        elif args.kotlin:
            settings = kotlin_settings()
        elif args.nim:
            settings = nim_settings()
        elif args.dart:
            settings = dart_settings()
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


if __name__ == "__main__":
    main()
