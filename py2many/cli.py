import argparse
import ast
import os
import pathlib
import subprocess

from dataclasses import dataclass
from typing import List, Optional

from .analysis import add_imports
from .clike import CLikeTranspiler
from .scope import add_scope_context
from .annotation_transformer import add_annotation_flags
from .mutability_transformer import detect_mutable_vars
from .nesting_transformer import detect_nesting_levels
from .context import add_variable_context, add_list_calls
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
    formatter: Optional[List[str]] = None
    indent: Optional[int] = None


def cpp_settings(args):
    return LanguageSettings(CppTranspiler(), ".cpp", ["clang-format", "-i"])


def rust_settings(args):
    return LanguageSettings(RustTranspiler(), ".rs", ["rustfmt"])


def julia_settings(args):
    return LanguageSettings(JuliaTranspiler(), ".jl", ["jlfmt"])


def kotlin_settings(args):
    return LanguageSettings(KotlinTranspiler(), ".kt", ["ktlint", "-F"])


def nim_settings(args):
    nim_args = {}
    if args.indent is not None:
        nim_args["indent"] = args.indent
    return LanguageSettings(NimTranspiler(**nim_args), ".nim", None)


def dart_settings(args):
    return LanguageSettings(DartTranspiler(), ".dart", ["dart", "format"])


def go_settings(args):
    return LanguageSettings(GoTranspiler(), ".go", ["gofmt", "-w"])


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
        f.write(transpile(source_data, settings.transpiler))
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
