import argparse
import ast
import functools
import os
import sys


from distutils import spawn
from functools import lru_cache
from pathlib import Path
from subprocess import run
from typing import List, Set, Tuple
from unittest.mock import Mock


from .analysis import add_imports
from .annotation_transformer import add_annotation_flags

from .context import add_assignment_context, add_variable_context, add_list_calls
from .exceptions import AstErrorBase
from .inference import infer_types
from .language import LanguageSettings
from .mutability_transformer import detect_mutable_vars
from .nesting_transformer import detect_nesting_levels
from .python_transformer import PythonTranspiler, RestoreMainRewriter
from .scope import add_scope_context
from .toposort_modules import toposort

from pycpp.transpiler import CppTranspiler, CppListComparisonRewriter
from pyrs.inference import infer_rust_types
from pyrs.transpiler import (
    RustTranspiler,
    RustLoopIndexRewriter,
    RustNoneCompareRewriter,
    RustStringJoinRewriter,
)
from pyjl.transpiler import JuliaTranspiler, JuliaMethodCallRewriter
from pykt.inference import infer_kotlin_types
from pykt.transpiler import KotlinTranspiler, KotlinPrintRewriter, KotlinBitOpRewriter
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
from pyv.inference import infer_v_types
from pyv.transpiler import VTranspiler, VNoneCompareRewriter, VDictRewriter

from py2many.rewriters import (
    ComplexDestructuringRewriter,
    FStringJoinRewriter,
    InferredAnnAssignRewriter,
    PythonMainRewriter,
    DocStringToCommentRewriter,
    PrintBoolRewriter,
    StrStrRewriter,
    WithToBlockTransformer,
    IgnoredAssignRewriter,
    UnpackScopeRewriter,
)

PY2MANY_DIR = Path(__file__).parent
ROOT_DIR = PY2MANY_DIR.parent
CWD = Path.cwd()


def core_transformers(tree, trees):
    add_variable_context(tree, trees)
    add_scope_context(tree)
    add_assignment_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    infer_meta = infer_types(tree)
    add_imports(tree)
    return tree, infer_meta


def _transpile(
    filenames: List[Path],
    sources: List[str],
    settings: LanguageSettings,
    _suppress_exceptions=Exception,
):
    """
    Transpile a single python translation unit (a python script) into
    target language
    """
    transpiler = settings.transpiler
    rewriters = settings.rewriters
    transformers = settings.transformers
    post_rewriters = settings.post_rewriters
    tree_list = []
    for filename, source in zip(filenames, sources):
        tree = ast.parse(source)
        tree.__file__ = filename
        tree_list.append(tree)
    trees = toposort(tree_list)
    topo_filenames = [t.__file__ for t in trees]
    language = transpiler.NAME
    generic_rewriters = [
        ComplexDestructuringRewriter(language),
        PythonMainRewriter(settings.transpiler._main_signature_arg_names),
        FStringJoinRewriter(language),
        DocStringToCommentRewriter(language),
        WithToBlockTransformer(language),
        IgnoredAssignRewriter(language),
    ]
    # Language independent rewriters that run after type inference
    generic_post_rewriters = [
        PrintBoolRewriter(language),
        StrStrRewriter(language),
        UnpackScopeRewriter(language),
    ]
    rewriters = generic_rewriters + rewriters
    post_rewriters = generic_post_rewriters + post_rewriters
    outputs = {}
    successful = []
    for filename, tree in zip(topo_filenames, trees):
        try:
            output = _transpile_one(
                trees, tree, transpiler, rewriters, transformers, post_rewriters
            )
            successful.append(filename)
            outputs[filename] = output
        except Exception as e:
            import traceback

            formatted_lines = traceback.format_exc().splitlines()
            if isinstance(e, AstErrorBase):
                print(f"{filename}:{e.lineno}:{e.col_offset}: {formatted_lines[-1]}")
            else:
                print(f"{filename}: {formatted_lines[-1]}")
            if not _suppress_exceptions or not isinstance(e, _suppress_exceptions):
                raise
            outputs[filename] = "FAILED"
    # return output in the same order as input
    output_list = [outputs[f] for f in filenames]
    return output_list, successful


def _transpile_one(trees, tree, transpiler, rewriters, transformers, post_rewriters):
    # This is very basic and needs to be run before and after
    # rewrites. Revisit if running it twice becomes a perf issue
    add_scope_context(tree)
    # Language specific rewriters
    for rewriter in rewriters:
        tree = rewriter.visit(tree)
    # Language independent core transformers
    tree, infer_meta = core_transformers(tree, trees)
    # Language specific transformers
    for tx in transformers:
        tx(tree)
    # Language specific rewriters that depend on previous steps
    for rewriter in post_rewriters:
        tree = rewriter.visit(tree)
    # Rerun core transformers
    tree, infer_meta = core_transformers(tree, trees)
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
    if transpiler.extension:
        out.append(transpiler.extension_module(tree))
    return "\n".join(out)


@lru_cache(maxsize=100)
def _process_one_data(source_data, filename, settings):
    return _transpile([filename], [source_data], settings)[0][0]


def _create_cmd(parts, filename, **kw):
    cmd = [arg.format(filename=filename, **kw) for arg in parts]
    if cmd != parts:
        return cmd
    return [*parts, str(filename)]


def python_settings(args, env=os.environ):
    return LanguageSettings(
        PythonTranspiler(),
        ".py",
        "Python",
        formatter=["black"],
        rewriters=[RestoreMainRewriter()],
        post_rewriters=[InferredAnnAssignRewriter()],
    )


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
    if cxx.startswith("clang++") and not sys.platform == "win32":
        cxx_flags += ["-stdlib=libc++"]

    if clang_format_style:
        clang_format_cmd = ["clang-format", f"-style={clang_format_style}", "-i"]
    else:
        clang_format_cmd = ["clang-format", "-i"]

    return LanguageSettings(
        CppTranspiler(args.extension, args.no_prologue),
        ".cpp",
        "C++",
        clang_format_cmd,
        None,
        [CppListComparisonRewriter()],
        linter=[cxx, *cxx_flags],
    )


def rust_settings(args, env=os.environ):
    return LanguageSettings(
        RustTranspiler(args.extension, args.no_prologue),
        ".rs",
        "Rust",
        ["rustfmt", "--edition=2018"],
        None,
        [RustNoneCompareRewriter()],
        [functools.partial(infer_rust_types, extension=args.extension)],
        [RustLoopIndexRewriter(), RustStringJoinRewriter()],
    )


def julia_settings(args, env=os.environ):
    format_jl = spawn.find_executable("format.jl")
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
        [],
        [],
        [JuliaMethodCallRewriter()],
    )


def kotlin_settings(args, env=os.environ):
    return LanguageSettings(
        KotlinTranspiler(),
        ".kt",
        "Kotlin",
        ["ktlint", "-F"],
        rewriters=[KotlinBitOpRewriter()],
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
        "Nim",
        ["nimpretty", *nimpretty_args],
        None,
        [NimNoneCompareRewriter()],
        [infer_nim_types],
    )


def dart_settings(args, env=os.environ):
    return LanguageSettings(
        DartTranspiler(),
        ".dart",
        "Dart",
        ["dart", "format"],
        post_rewriters=[DartIntegerDivRewriter()],
    )


def go_settings(args, env=os.environ):
    config_filename = "revive.toml"
    if os.path.exists(CWD / config_filename):
        revive_config = CWD / config_filename
    elif os.path.exists(PY2MANY_DIR / config_filename):
        revive_config = PY2MANY_DIR / config_filename
    else:
        revive_config = None
    return LanguageSettings(
        GoTranspiler(),
        ".go",
        "Go",
        ["gofmt", "-w"],
        None,
        [GoNoneCompareRewriter(), GoVisibilityRewriter(), GoIfExpRewriter()],
        [infer_go_types],
        [GoMethodCallRewriter(), GoPropagateTypeAnnotation()],
        linter=(
            ["revive", "--config", str(revive_config)] if revive_config else ["revive"]
        ),
    )


def vlang_settings(args, env=os.environ):
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
        [VNoneCompareRewriter(), VDictRewriter()],
        [infer_v_types],
    )


def _get_all_settings(args, env=os.environ):
    return {
        "python": python_settings(args, env=env),
        "cpp": cpp_settings(args, env=env),
        "rust": rust_settings(args, env=env),
        "julia": julia_settings(args, env=env),
        "kotlin": kotlin_settings(args, env=env),
        "nim": nim_settings(args, env=env),
        "dart": dart_settings(args, env=env),
        "go": go_settings(args, env=env),
        "vlang": vlang_settings(args, env=env),
    }


def _relative_to_cwd(absolute_path):
    return Path(os.path.relpath(absolute_path, CWD))


def _get_output_path(filename, ext, outdir):
    directory = outdir / filename.parent
    if not directory.is_dir():
        directory.mkdir(parents=True)
    output_path = directory / (filename.stem + ext)
    if ext == ".kt" and output_path.is_absolute():
        # KtLint does not support absolute path in globs
        output_path = _relative_to_cwd(output_path)
    return output_path


def _process_one(settings: LanguageSettings, filename: Path, outdir: str, args, env):
    """Transpile and reformat.

    Returns False if reformatter failed.
    """
    suffix = f".{args.suffix}" if args.suffix is not None else settings.ext
    output_path = _get_output_path(
        filename.relative_to(filename.parent), suffix, outdir
    )
    if filename.resolve() == output_path.resolve() and not args.force:
        print(f"Refusing to overwrite {filename}. Use --force to overwrite")
        return False

    print(f"{filename} ... {output_path}")
    with open(filename) as f:
        source_data = f.read()
    dunder_init = filename.stem == "__init__"
    if dunder_init and not source_data:
        print("Detected empty __init__; skipping")
        return True
    result = _transpile([filename], [source_data], settings)
    with open(output_path, "w") as f:
        f.write(result[0][0])

    if settings.formatter:
        return _format_one(settings, output_path, env)

    return True


def _format_one(settings, output_path, env=None):
    try:
        restore_cwd = False
        if settings.ext == ".kt" and output_path.parts[0] == "..":
            # ktlint can not handle relative paths starting with ..
            restore_cwd = CWD

            os.chdir(output_path.parent)
            output_path = output_path.name
        cmd = _create_cmd(settings.formatter, filename=output_path)
        proc = run(cmd, env=env, capture_output=True)
        if proc.returncode:
            # format.jl exit code is unreliable
            if settings.ext == ".jl":
                if proc.stderr is not None:
                    print(
                        f"{cmd} (code: {proc.returncode}):\n{proc.stderr}{proc.stdout}"
                    )
                    if b"ERROR: " in proc.stderr:
                        return False
                return True
            print(
                f"Error: {cmd} (code: {proc.returncode}):\n{proc.stderr}{proc.stdout}"
            )
            if restore_cwd:
                os.chdir(restore_cwd)
            return False
        if settings.ext == ".kt":
            # ktlint formatter needs to be invoked twice before output is lint free
            if run(cmd, env=env).returncode:
                print(f"Error: Could not reformat: {cmd}")
                if restore_cwd:
                    os.chdir(restore_cwd)
                return False

        if restore_cwd:
            os.chdir(restore_cwd)
    except Exception as e:
        print(f"Error: Could not format: {output_path}")
        print(f"Due to: {e.__class__.__name__} {e}")
        return False

    return True


FileSet = Set[Path]


def _process_many(
    settings, basedir, filenames, outdir, env=None, _suppress_exceptions=Exception
) -> Tuple[FileSet, FileSet]:
    """Transpile and reformat many files."""

    # Try to flush out as many errors as possible
    settings.transpiler.set_continue_on_unimplemented()

    source_data = []
    for filename in filenames:
        with open(basedir / filename) as f:
            source_data.append(f.read())

    outputs, successful = _transpile(
        filenames,
        source_data,
        settings,
        _suppress_exceptions=_suppress_exceptions,
    )

    output_paths = [
        _get_output_path(filename, settings.ext, outdir) for filename in filenames
    ]
    for filename, output, output_path in zip(filenames, outputs, output_paths):
        with open(output_path, "w") as f:
            f.write(output)

    successful = set(successful)
    format_errors = set()
    if settings.formatter:
        # TODO: Optimize to a single invocation
        for filename, output_path in zip(filenames, output_paths):
            if filename in successful and not _format_one(settings, output_path, env):
                format_errors.add(Path(filename))

    return (successful, format_errors)


def _process_dir(settings, source, outdir, env=None, _suppress_exceptions=Exception):
    print(f"Transpiling whole directory to {outdir}:")
    successful = []
    failures = []
    input_paths = []
    for path in source.rglob("*.py"):
        if path.suffix != ".py":
            continue
        if path.parent.name == "__pycache__":
            continue

        relative_path = path.relative_to(source)
        target_path = outdir / relative_path
        target_dir = target_path.parent
        os.makedirs(target_dir, exist_ok=True)
        input_paths.append(relative_path)

    successful, format_errors = _process_many(
        settings,
        source,
        input_paths,
        outdir,
        env=env,
        _suppress_exceptions=_suppress_exceptions,
    )
    failures = set(input_paths) - set(successful)

    print("\nFinished!")
    print(f"Successful: {len(successful)}")
    if format_errors:
        print(f"Failed to reformat: {len(format_errors)}")
    print(f"Failed to convert: {len(failures)}")
    print()
    return (successful, format_errors, failures)


def main(args=None, env=os.environ):
    parser = argparse.ArgumentParser()
    LANGS = _get_all_settings(Mock(indent=4))
    for lang, settings in LANGS.items():
        parser.add_argument(
            f"--{lang}",
            type=bool,
            default=False,
            help=f"Generate {settings.display_name} code",
        )
    parser.add_argument("--outdir", default=None, help="Output directory")
    parser.add_argument(
        "-i",
        "--indent",
        type=int,
        default=None,
        help="Indentation to use in languages that care",
    )
    parser.add_argument(
        "--comment-unsupported",
        default=False,
        action="store_true",
        help="Place unsupported constructs in comments",
    )
    parser.add_argument(
        "--extension",
        action="store_true",
        default=False,
        help="Build a python extension",
    )
    parser.add_argument(
        "--suffix",
        default=None,
        help="Alternate suffix to use instead of the default one for the language",
    )
    parser.add_argument("--no-prologue", action="store_true", default=False, help="")
    parser.add_argument(
        "--force",
        action="store_true",
        default=False,
        help="When output and input are the same file, force overwriting",
    )
    args, rest = parser.parse_known_args(args=args)

    # Validation of the args
    if args.extension and not args.rust:
        print("extension supported only with rust via pyo3")
        return -1

    if args.comment_unsupported:
        print("Wrapping unimplemented in comments")

    for filename in rest:
        settings = cpp_settings(args, env=env)
        if args.cpp:
            pass
        if args.rust:
            settings = rust_settings(args, env=env)
        elif args.python:
            settings = python_settings(args, env=env)
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
        elif args.vlang:
            settings = vlang_settings(args, env=env)

        if args.comment_unsupported:
            settings.transpiler._throw_on_unimplemented = False

        source = Path(filename)
        if args.outdir is None:
            outdir = source.parent
        else:
            outdir = Path(args.outdir)

        if source.is_file():
            print(f"Writing to: {outdir}")
            try:
                rv = _process_one(settings, source, outdir, args, env)
            except Exception as e:
                import traceback

                formatted_lines = traceback.format_exc().splitlines()
                if isinstance(e, AstErrorBase):
                    print(f"{source}:{e.lineno}:{e.col_offset}: {formatted_lines[-1]}")
                else:
                    print(f"{source}: {formatted_lines[-1]}")
                rv = False
        else:
            if args.outdir is None:
                outdir = source.parent / f"{source.name}-py2many"

            successful, format_errors, failures = _process_dir(
                settings, source, outdir, env=env
            )
            rv = not (failures or format_errors)
        rv = 0 if rv is True else 1
        return rv
