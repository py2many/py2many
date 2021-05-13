import argparse
import ast
import os
import pathlib

from dataclasses import dataclass, field
from distutils import spawn
from subprocess import run
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
    RustStringJoinRewriter,
)
from pyjl.transpiler import JuliaTranspiler, JuliaMethodCallRewriter
from pykt.inference import infer_kotlin_types
from pykt.transpiler import KotlinTranspiler, KotlinPrintRewriter
from pynim.inference import infer_nim_types
from pynim.transpiler import NimTranspiler, NimNoneCompareRewriter
from pydart.transpiler import DartTranspiler, DartIntegerDivRewriter
from pygo.inference import infer_go_types
from pygo.transpiler import (
    GoTranspiler,
    GoMethodCallRewriter,
    GoNoneCompareRewriter,
    GoPropagateTypeAnnotation,
    GoVisibilityRewriter,
    GoIfExpRewriter,
)

from py2many.rewriters import (
    ComplexDestructuringRewriter,
    FStringJoinRewriter,
    PythonMainRewriter,
    DocStringToCommentRewriter,
    PrintBoolRewriter,
)

PY2MANY_DIR = pathlib.Path(__file__).parent
ROOT_DIR = PY2MANY_DIR.parent


def core_transformers(tree):
    add_variable_context(tree)
    add_scope_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    infer_meta = infer_types(tree)
    add_imports(tree)
    return tree, infer_meta


def transpile(source, transpiler, rewriters, transformers, post_rewriters):
    """
    Transpile a single python translation unit (a python script) into
    Rust code.
    """
    if isinstance(source, ast.Module):
        tree = source
    else:
        tree = ast.parse(source)
    language = transpiler.NAME
    generic_rewriters = [
        ComplexDestructuringRewriter(language),
        PythonMainRewriter(language),
        FStringJoinRewriter(language),
        DocStringToCommentRewriter(language),
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
    # Language independent core transformers
    tree, infer_meta = core_transformers(tree)
    # Language specific transformers
    for tx in transformers:
        tx(tree)
    # Language independent rewriters that run after type inference
    generic_post_rewriters = [PrintBoolRewriter(language)]
    for rewriter in generic_post_rewriters:
        tree = rewriter.visit(tree)
    # Language specific rewriters that depend on previous steps
    for rewriter in post_rewriters:
        tree = rewriter.visit(tree)
    # Rerun core transformers
    tree, infer_meta = core_transformers(tree)
    out = []
    code = transpiler.visit(tree) + "\n"
    headers = transpiler.headers(infer_meta)
    features = transpiler.features()
    if features:
        out.append(features)
    if headers:
        out.append(headers)
    usings = transpiler.usings()
    if usings:
        out.append(usings)
    out.append(code)
    return "\n".join(out)


def _create_cmd(parts, filename):
    cmd = [arg.format(filename=filename) for arg in parts]
    if cmd != parts:
        return cmd
    return [*parts, str(filename)]


@dataclass
class LanguageSettings:
    transpiler: CLikeTranspiler
    ext: str
    formatter: Optional[List[str]] = None
    indent: Optional[int] = None
    rewriters: List[ast.NodeVisitor] = field(default_factory=list)
    transformers: List[Callable] = field(default_factory=list)
    post_rewriters: List[ast.NodeVisitor] = field(default_factory=list)
    linter: Optional[List[str]] = None


def cpp_settings(args, env=os.environ):
    clang_format_style = env.get("CLANG_FORMAT_STYLE")
    cxx = env.get("CXX")
    default_cxx = ["clang++", "g++-11", "g++"]
    if cxx:
        if not spawn.find_executable(cxx):
            print(f"Warning: CXX({cxx}) not found")
            cxx = None
    if not cxx:
        for exe in default_cxx:
            if spawn.find_executable(exe):
                cxx = exe
                break
        else:
            cxx = default_cxx[0]
    cxx_flags = env.get("CXXFLAGS")
    if cxx_flags:
        cxx_flags = cxx_flags.split()
    else:
        cxx_flags = ["-std=c++14", "-Wall", "-Werror"]
    cxx_flags = ["-I", str(ROOT_DIR)] + cxx_flags
    if cxx == "clang++":
        cxx_flags += ["-stdlib=libc++"]

    if clang_format_style:
        clang_format_cmd = ["clang-format", f"-style={clang_format_style}", "-i"]
    else:
        clang_format_cmd = ["clang-format", "-i"]

    return LanguageSettings(
        CppTranspiler(),
        ".cpp",
        clang_format_cmd,
        None,
        [CppListComparisonRewriter()],
        linter=[cxx, *cxx_flags],
    )


def rust_settings(args, env=os.environ):
    return LanguageSettings(
        RustTranspiler(),
        ".rs",
        ["rustfmt", "--edition=2018"],
        None,
        [RustNoneCompareRewriter()],
        [infer_rust_types],
        [RustLoopIndexRewriter(), RustStringJoinRewriter()],
    )


def julia_settings(args, env=os.environ):
    format_jl = spawn.find_executable("format.jl")
    if format_jl:
        format_jl = ["julia", "-O0", "--compile=min", "--startup=no", format_jl, "-v"]
    else:
        format_jl = ["format.jl", "-v"]
    return LanguageSettings(
        JuliaTranspiler(), ".jl", format_jl, None, [], [], [JuliaMethodCallRewriter()]
    )


def kotlin_settings(args, env=os.environ):
    return LanguageSettings(
        KotlinTranspiler(),
        ".kt",
        ["ktlint", "-F"],
        transformers=[infer_kotlin_types],
        post_rewriters=[KotlinPrintRewriter()],
        linter=["ktlint"],
    )


def nim_settings(args, env=os.environ):
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


def dart_settings(args, env=os.environ):
    return LanguageSettings(
        DartTranspiler(),
        ".dart",
        ["dart", "format"],
        post_rewriters=[DartIntegerDivRewriter()],
    )


def go_settings(args, env=os.environ):
    return LanguageSettings(
        GoTranspiler(),
        ".go",
        ["gofmt", "-w"],
        None,
        [GoNoneCompareRewriter(), GoVisibilityRewriter(), GoIfExpRewriter()],
        [infer_go_types],
        [GoMethodCallRewriter(), GoPropagateTypeAnnotation()],
        linter=["golint", "-set_exit_status", "-min_confidence", "1.0"],
    )


def _get_all_settings(args, env=os.environ):
    return {
        "cpp": cpp_settings(args, env=env),
        "rust": rust_settings(args, env=env),
        "julia": julia_settings(args, env=env),
        "kotlin": kotlin_settings(args, env=env),
        "nim": nim_settings(args, env=env),
        "dart": dart_settings(args, env=env),
        "go": go_settings(args, env=env),
    }


def _process_once(settings, filename, outdir, env=None):
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
        cmd = _create_cmd(settings.formatter, output_path)
        proc = run(cmd, env=env)
        if proc.returncode:
            # format.jl exit code is unreliable
            if settings.ext == ".jl":
                if proc.stderr is not None:
                    print(
                        f"Error: {cmd} (code: {proc.returncode}):\n{proc.stderr}{proc.stdout}"
                    )
                return True
            print(
                f"Error: {cmd} (code: {proc.returncode}):\n{proc.stderr}{proc.stdout}"
            )
            return False
        if settings.ext == ".kt":
            # ktlint formatter needs to be invoked twice before output is lint free
            if run(cmd, env=env).returncode:
                print(f"Error: Could not reformat: {cmd}")
                return False
    return True


def main(args=None, env=os.environ):
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
    args, rest = parser.parse_known_args(args=args)
    for filename in rest:
        settings = cpp_settings(args, env=env)
        if args.cpp:
            pass
        if args.rust:
            settings = rust_settings(args, env=env)
        elif args.julia:
            settings = julia_settings(args, env=env)
        elif args.kotlin:
            settings = kotlin_settings(args, env=env)
        elif args.nim:
            settings = nim_settings(args, env=env)
        elif args.dart:
            settings = dart_settings(args, env=env)
        elif args.go:
            settings = go_settings(args, env=env)
        source = pathlib.Path(filename)
        if args.outdir is None:
            outdir = source.parent
        else:
            outdir = pathlib.Path(args.outdir)

        if source.is_file():
            print(f"Writing to: {outdir}")
            rv = _process_once(settings, source, outdir, env=env)
        else:
            if args.outdir is None:
                outdir = source.parent / f"{source.name}-py2many"

            print(f"Transpiling whole directory to {outdir}:")
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
                    if _process_once(settings, path, target_dir, env=env):
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
            rv = not failures or format_errors
        return rv
