#!/usr/bin/env python3

import argparse
import ast
import os
import pathlib

from common.clike import CLikeTranspiler
from common.scope import add_scope_context
from common.annotation_transformer import add_annotation_flags
from common.mutability_transformer import detect_mutable_vars
from common.context import add_variable_context, add_list_calls
from common.analysis import add_imports, is_void_function, get_id, is_mutable
from dataclasses import dataclass

from py14.transpiler import CppTranspiler
from pyrs.transpiler import RustTranspiler
from pyjl.transpiler import JuliaTranspiler


def transpile(source, transpiler):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    tree = ast.parse(source)
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    add_annotation_flags(tree)
    add_imports(tree)

    return transpiler.visit(tree) + "\n"


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
    return LanguageSettings(JuliaTranspiler(), ".jl", "/bin/true")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpp", type=bool, default=False, help="Generate C++ code")
    parser.add_argument("--rust", type=bool, default=False, help="Generate Rust code")
    parser.add_argument("--julia", type=bool, default=False, help="Generate Julia code")
    parser.add_argument("--outdir", default=None, help="Output directory")
    args, rest = parser.parse_known_args()
    for filename in rest:
        settings = cpp_settings()
        if args.cpp:
            pass
        if args.rust:
            settings = rust_settings()
        if args.julia:
            settings = julia_settings()
        source = pathlib.Path(filename)
        if args.outdir is None:
            outdir = source.parent
        else:
            outdir = pathlib.Path(args.outdir)
        print(f"Writing to: {outdir}")
        output_path = outdir / (source.stem + settings.ext)
        print(f"{filename}...")
        with open(output_path, "w") as f:
            source_data = open(source).read()
            f.write(transpile(source_data, settings.transpiler))
        os.system(f"{settings.formatter} {output_path}")
        print()


if __name__ == "__main__":
    main()
