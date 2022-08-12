import argparse
import ast
import builtins
import os
import functools
import string

import sys
import tempfile


from distutils import spawn
from functools import lru_cache
from pathlib import Path
from subprocess import run
from typing import List, Optional, Set, Tuple
from unittest.mock import Mock

from py2many.input_configuration import config_rewriters, parse_input_configurations
from py2many.pytype_inference import pytype_annotate_and_merge
from pyjl.optimizations import AlgebraicSimplification, OperationOptimizer, PerformanceOptimizations
from pynim.rewriters import WithToBlockRewriter


from .analysis import add_imports

from .context import add_assignment_context, add_variable_context, add_list_calls
from .exceptions import AstErrorBase
from .inference import infer_types, infer_types_typpete
from .language import LanguageSettings
from .transformers import (
    add_annotation_flags,
    correct_node_attributes,
    detect_mutable_vars,
    detect_nesting_levels,
)
from .scope import add_scope_context
from .toposort_modules import toposort

from py2py.transpiler import PythonTranspiler
from pycpp.transpiler import CppTranspiler, CppListComparisonRewriter
from pyrs.inference import infer_rust_types
from pyrs.transpiler import (
    RustTranspiler,
    RustLoopIndexRewriter,
    RustNoneCompareRewriter,
    RustStringJoinRewriter,
)

from pyjl.analysis import analyse_variable_scope, detect_broadcast, loop_range_optimization_analysis
from pyjl.transformers import find_ordered_collections, parse_decorators
from pyjl.rewriters import (
    JuliaArgumentParserRewriter,
    JuliaImportNameRewriter,
    VariableScopeRewriter,
    JuliaArbitraryPrecisionRewriter,
    JuliaIORewriter,
    JuliaImportRewriter,
    JuliaAugAssignRewriter,
    JuliaGeneratorRewriter,
    JuliaConditionRewriter,
    JuliaIndexingRewriter,
    JuliaMainRewriter,
    JuliaMethodCallRewriter,
    JuliaModuleRewriter,
    JuliaOffsetArrayRewriter,
    JuliaOrderedCollectionRewriter,
    JuliaCTypesRewriter, 
    JuliaClassWrapper, 
    JuliaIndexingRewriter, 
    JuliaNestingRemoval
)
from pyjl.transpiler import JuliaTranspiler
from pyjl.inference import infer_julia_types

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
from pyv.transpiler import (
    VTranspiler,
    VNoneCompareRewriter,
    VDictRewriter,
    VComprehensionRewriter,
)
from pysmt.transpiler import SmtTranspiler
from pysmt.inference import infer_smt_types

from py2many.rewriters import (
    ComplexDestructuringRewriter,
    FStringJoinRewriter,
    LoopElseRewriter,
    InferredAnnAssignRewriter,
    UnitTestRewriter,
    PythonMainRewriter,
    DocStringToCommentRewriter,
    PrintBoolRewriter,
    StrStrRewriter,
    IgnoredAssignRewriter,
    UnpackScopeRewriter,
)

PY2MANY_DIR = Path(__file__).parent
ROOT_DIR = PY2MANY_DIR.parent
STDIN = "-"
STDOUT = "-"
CWD = Path.cwd()
USER_HOME = os.path.expanduser("~/")


def core_transformers(tree, trees, args):
    add_variable_context(tree, trees)
    add_scope_context(tree)
    add_assignment_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    add_annotation_flags(tree)
    add_imports(tree)
    correct_node_attributes(tree)
    return tree


def _transpile(
    filenames: List[Path],
    sources: List[str],
    settings: LanguageSettings,
    args: Optional[argparse.Namespace] = None,
    _suppress_exceptions=Exception,
    basedir: str = None,
):
    """
    Transpile a single python translation unit (a python script) into
    target language
    """
    transpiler = settings.transpiler
    inference = settings.inference \
        if settings.inference else infer_types
    rewriters = settings.rewriters
    transformers = settings.transformers
    post_rewriters = settings.post_rewriters
    optimization_rewriters = settings.optimization_rewriters
    tree_list = []

    if args.pytype:
        # Pytype only parses code as string at the moment
        inferred_sources = []
        for filename, source in zip(filenames, sources):
            inferred_sources.append(pytype_annotate_and_merge(source, basedir, filename))
        sources = inferred_sources

    for filename, source in zip(filenames, sources):
        tree = ast.parse(source, type_comments=True)
        tree.__file__ = filename
        tree.__basedir__ = basedir
        tree_list.append(tree)
    trees = toposort(tree_list)
    topo_filenames = [t.__file__ for t in trees]
    language = transpiler.NAME
    generic_rewriters = [
        ComplexDestructuringRewriter(language),
        DocStringToCommentRewriter(language),
        IgnoredAssignRewriter(language),
    ]

    if settings.ext != ".jl":
        generic_rewriters.append(FStringJoinRewriter(language))
    if settings.ext != ".jl" and settings.ext != ".py":
        generic_rewriters.append(
            PythonMainRewriter(settings.transpiler._main_signature_arg_names)
        )

    # Language independent rewriters that run after type inference
    generic_post_rewriters = [
        PrintBoolRewriter(language),
        StrStrRewriter(language),
        UnpackScopeRewriter(language),
        LoopElseRewriter(language),
        UnitTestRewriter(language),
    ]
    rewriters = generic_rewriters + rewriters
    post_rewriters = generic_post_rewriters + post_rewriters

    # Handle input configuration files
    config_handler = None
    if args.config:
        config_handler = parse_input_configurations(args.config)

    outputs = {}
    successful = []
    for filename, tree in zip(topo_filenames, trees):
        try:
            output = _transpile_one(
                trees,
                tree,
                transpiler,
                rewriters,
                transformers,
                post_rewriters,
                optimization_rewriters,
                inference,
                config_handler,
                args,
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
            # outputs[filename] = str(e)

    # return output in the same order as input
    output_list = [outputs[f] for f in filenames]

    return output_list, successful


def _transpile_one(
    trees,
    tree,
    transpiler,
    rewriters,
    transformers,
    post_rewriters,
    optimization_rewriters,
    inference,
    config_handler,
    args,
):
    # This is very basic and needs to be run before and after
    # rewrites. Revisit if running it twice becomes a perf issue
    add_scope_context(tree)
    # Configuration parser
    if config_handler:
        config_rewriters(config_handler, tree)
    # Language specific rewriters
    for rewriter in rewriters:
        tree = rewriter.visit(tree)
    # Language independent core transformers
    tree = core_transformers(tree, trees, args)
    # Type inference
    if args and args.typpete:
        infer_meta = infer_types_typpete(tree)
    else:
        infer_meta = inference(tree)
    # Language specific transformers
    for tx in transformers:
        tx(tree)
    # Language specific rewriters that depend on previous steps
    for rewriter in post_rewriters:
        tree = rewriter.visit(tree)
    # Language specific optimizations
    for opt_rewriter in optimization_rewriters:
        tree = opt_rewriter.visit(tree)

    # Rerun core transformers
    tree = core_transformers(tree, trees, args)
    out = []


    transpile_output = transpiler.visit(tree)
    headers = transpiler.headers(infer_meta)
    if headers:
        out.append(headers)
    out.append(transpile_output)
    if transpiler.extension:
        out.append(transpiler.extension_module(tree))
    return "\n".join(out)


@lru_cache(maxsize=100)
def _process_one_data(source_data, filename, settings, args, basedir):
    return _transpile([filename], [source_data], settings, args, outdir=basedir)[0][0]


def _create_cmd(parts, filename, **kw):
    cmd = [arg.format(filename=filename, **kw) for arg in parts]
    if cmd != parts:
        return cmd
    return [*parts, str(filename)]


def _parse_expected(outputs, settings, args):
    """Check if files match the expected results"""

    file_out = args.expected
    if os.path.isdir(file_out):
        dir_files = []
        for f in os.listdir(file_out):
            dir_files.append(f.split(".")[0])
        for (f_name, path) in outputs:
            name: str = f_name.name.split(".")[0]
            if name in dir_files:
                comp_res = _compare_file_contents(
                    f"{file_out}/{name}{settings.ext}", f"{path}"
                )
                if not comp_res:
                    print(f"{name} does not have expected result")
    elif os.path.isfile(file_out):
        file_name, file_ext = file_out.split(".")
        if file_ext != settings.ext:
            raise Exception("Attempting to parse a file with an incompatibel exception")
        if len(outputs) > 1:
            raise Exception(
                "Attempting to parse one expected file with multiple outputs"
            )

        return _compare_file_contents(f"{file_out}", f"{path}")
    else:
        raise Exception(
            f"Could not parse expected files. {file_out} could not be found."
        )


def _compare_file_contents(file1_path, file2_path):
    """Compares file contents for equality"""

    # Read data from files
    expected_data = None
    curr_file_data = None
    with open(file1_path, encoding="utf-8") as f1, open(
        file2_path, encoding="utf-8"
    ) as f2:
        expected_data = f1.read()
        curr_file_data = f2.read()

    if expected_data == None or curr_file_data == None:
        raise Exception(f"File {file1_path} does not have an expected result file")

    # Check if files match
    remove = string.whitespace
    mapping = {ord(c): None for c in remove}
    data: str = expected_data.translate(mapping)
    contents: str = curr_file_data.translate(mapping)
    return contents == data


def python_settings(args, env=os.environ):
    return LanguageSettings(
        PythonTranspiler(),
        ".py",
        "Python",
        formatter=["black"],
        rewriters=[],
        post_rewriters=[InferredAnnAssignRewriter()],
    )


def _conan_include_dirs():
    CONAN_CATCH2 = "catch2/3.0.1/_/_/package/a25d6c83542b56b72fdaa05a85db5d46f5f0f71c"
    CONAN_CPPITERTOOLS = (
        "cppitertools/2.1/_/_/package/5ab84d6acfe1f23c4fae0ab88f26e3a396351ac9"
    )
    return [
        "-I",
        f"{USER_HOME}/.conan/data/{CONAN_CATCH2}/include",
        "-I",
        f"{USER_HOME}/.conan/data/{CONAN_CPPITERTOOLS}/include",
    ]


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
        cxx_flags = ["-std=c++17", "-Wall", "-Werror"]
    cxx_flags = ["-I", str(ROOT_DIR)] + _conan_include_dirs() + cxx_flags
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
        rewriters=[RustNoneCompareRewriter()],
        transformers=[],
        post_rewriters=[RustLoopIndexRewriter(), RustStringJoinRewriter()],
        create_project=["cargo", "new", "--bin"],
        project_subdir="src",
        inference = functools.partial(infer_rust_types, extension=args.extension),
    )


@lru_cache()
def _julia_formatter_path():
    proc = run(
        ["julia", "-e", "import JuliaFormatter;print(pathof(JuliaFormatter))"],
        capture_output=True,
    )
    if not proc.returncode and proc.stdout:
        return str(Path(proc.stdout.decode("utf8")).parent.parent / "bin" / "format.jl")


def julia_settings(args, env=os.environ):
    format_jl = spawn.find_executable("format.jl")
    if not format_jl:
        julia = spawn.find_executable("julia")
        if julia:
            format_jl = _julia_formatter_path()

    if format_jl:
        format_jl = ["julia", "-O0", "--compile=min", "--startup=no", format_jl, "-v"]
    else:
        format_jl = ["format.jl", "-v"]

    return LanguageSettings(
        transpiler=JuliaTranspiler(),
        ext=".jl",
        display_name="Julia",
        formatter=format_jl,
        indent=None,
        rewriters=[
            JuliaMainRewriter(),
            JuliaImportNameRewriter()],
        transformers=[
            parse_decorators,
            analyse_variable_scope,
            loop_range_optimization_analysis,
            find_ordered_collections,
            detect_broadcast,
        ],
        post_rewriters=[
            JuliaNestingRemoval(),
            JuliaImportRewriter(),
            JuliaGeneratorRewriter(),
            JuliaOffsetArrayRewriter(),
            JuliaIndexingRewriter(),
            JuliaOrderedCollectionRewriter(),
            JuliaCTypesRewriter(),
            JuliaArgumentParserRewriter(),
            JuliaClassWrapper(),
            JuliaMethodCallRewriter(),
            JuliaAugAssignRewriter(),
            JuliaConditionRewriter(),
            VariableScopeRewriter(),
            JuliaModuleRewriter(),
            JuliaIORewriter(),
            JuliaArbitraryPrecisionRewriter(),
        ],
        optimization_rewriters=[
            AlgebraicSimplification(), 
            OperationOptimizer(), 
            PerformanceOptimizations()],
        inference = infer_julia_types
    )


def kotlin_settings(args, env=os.environ):
    return LanguageSettings(
        KotlinTranspiler(),
        ".kt",
        "Kotlin",
        ["ktlint", "-F"],
        rewriters=[KotlinBitOpRewriter()],
        post_rewriters=[KotlinPrintRewriter()],
        linter=["ktlint"],
        inference = infer_kotlin_types
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
        [NimNoneCompareRewriter(), WithToBlockRewriter],
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
        [],
        [GoMethodCallRewriter(), GoPropagateTypeAnnotation()],
        linter=(
            ["revive", "--config", str(revive_config)] if revive_config else ["revive"]
        ),
        inference = infer_go_types
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
        [VNoneCompareRewriter(), VDictRewriter(), VComprehensionRewriter()],
        [],
        inference = infer_v_types
    )


def smt_settings(args, env=os.environ):
    smt_args = {}
    cljstyle_args = ["fix"]
    return LanguageSettings(
        SmtTranspiler(**smt_args),
        ".smt",
        "SMT",
        ["cljstyle", *cljstyle_args],
        None,
        [],
        [infer_smt_types],
        inference = infer_smt_types
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
        "smt": smt_settings(args, env=env),
    }


def _relative_to_cwd(absolute_path):
    return Path(os.path.relpath(absolute_path, CWD))


def _get_output_path(filename, ext, outdir):
    if filename.name == STDIN:
        return Path(STDOUT)
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

    if filename.name == STDIN:
        # special case for simple pipes
        output = _process_one_data(
            sys.stdin.read(), Path("test.py"), settings, args, filename
        )
        tmp_name = None
        try:
            with tempfile.NamedTemporaryFile(suffix=settings.ext, delete=False) as f:
                tmp_name = f.name
                f.write(output.encode("utf-8"))
            if _format_one(settings, tmp_name, env):
                sys.stdout.write(open(tmp_name).read())
            else:
                sys.stderr.write("Formatting failed")
        finally:
            if tmp_name is not None:
                os.remove(tmp_name)
        return ({filename}, {filename})

    if filename.resolve() == output_path.resolve() and not args.force:
        print(f"Refusing to overwrite {filename}. Use --force to overwrite")
        return False

    print(f"{filename} ... {output_path}")
    with open(filename, encoding="utf-8") as f:
        source_data = f.read()
    dunder_init = filename.stem == "__init__"
    if dunder_init and not source_data:
        print("Detected empty __init__; skipping")
        return True
    result = _transpile([filename], [source_data], settings, args, basedir=filename)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(result[0][0])

    format_res = False
    if settings.formatter:
        print("Formatting file")
        format_res = _format_one(settings, output_path, env)

    # Compare with expected
    if hasattr(args, "expected") and args.expected is not None:
        _parse_expected([(filename, output_path)], settings, args)

    return format_res


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
    settings, basedir, filenames, outdir, args, env=None, _suppress_exceptions=Exception
) -> Tuple[FileSet, FileSet]:
    """Transpile and reformat many files."""

    # Try to flush out as many errors as possible
    settings.transpiler.set_continue_on_unimplemented()

    source_data = []
    for filename in filenames:
        with open(basedir / filename, encoding="utf-8") as f:
            source_data.append(f.read())

    outputs, successful = _transpile(
        filenames,
        source_data,
        settings,
        args,
        _suppress_exceptions=_suppress_exceptions,
        basedir=basedir,
    )

    output_paths = [
        _get_output_path(filename, settings.ext, outdir) for filename in filenames
    ]
    for filename, output, output_path in zip(filenames, outputs, output_paths):
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(output)

    successful = set(successful)
    format_errors = set()
    if settings.formatter:
        if settings.ext == ".jl":
            # Julia Formatter can receive multiple files
            _format_one(settings, outdir, env)
        else:
            # TODO: Optimize to a single invocation
            for filename, output_path in zip(filenames, output_paths):
                if filename in successful and not _format_one(
                    settings, output_path, env
                ):
                    format_errors.add(Path(filename))

    # Compare with expected
    if hasattr(args, "expected") and args.expected is not None:
        _parse_expected(zip(filenames, output_paths), settings, args)

    return (successful, format_errors)


def _process_dir(
    settings, source, outdir, args, env=None, _suppress_exceptions=Exception
):
    print(f"Transpiling whole directory to {outdir}:")

    if settings.create_project is not None and args.project:
        cmd = settings.create_project + [f"{outdir}"]
        proc = run(cmd, env=env, capture_output=True)
        if proc.returncode:
            cmd_str = " ".join(cmd)
            print(f"Error: running {cmd_str}: {proc.stderr}")
            return (set(), set(), set())
        if settings.project_subdir is not None:
            outdir = outdir / settings.project_subdir

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
        args,
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
    parser.add_argument(
        "--typpete",
        action="store_true",
        default=False,
        help="Use typpete for inference",
    )
    parser.add_argument(
        "--pytype",
        action="store_true",
        default=False,
        help="Use pytype for inference",
    )
    parser.add_argument(
        "--project", default=True, help="Create a project when using directory mode"
    )

    # Configuration files.
    parser.add_argument(
        "--config",
        default=None,
        help="External annotations with additional transpilation information",
    )

    # Compare files to expected
    parser.add_argument(
        "--expected",
        default=None,
        help="Directory containing expected results for comparison",
    )

    args, rest = parser.parse_known_args(args=args)

    # Validation of the args
    if args.extension and not args.rust:
        print("extension supported only with rust via pyo3")
        return -1

    if args.comment_unsupported:
        print("Wrapping unimplemented in comments")

    if len(rest) == 0:
        # Default is to consume stdin and write to stdout
        rest = [STDIN]
        args.outdir = STDOUT

    for filename in rest:
        source = Path(filename)

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
        elif args.smt:
            settings = smt_settings(args, env=env)

        if args.comment_unsupported:
            settings.transpiler._throw_on_unimplemented = False

        if args.outdir is None:
            outdir = source.parent
        else:
            outdir = Path(args.outdir)

        if source.is_file() or source.name == STDIN:
            print(f"Writing to: {outdir}", file=sys.stderr)
            try:
                rv = _process_one(settings, source, outdir, args, env)
            except Exception as e:
                import traceback

                formatted_lines = traceback.format_exc().splitlines()
                if isinstance(e, AstErrorBase):
                    print(
                        f"{source}:{e.lineno}:{e.col_offset}: {formatted_lines[-1]}",
                        file=sys.stderr,
                    )
                else:
                    print(f"{source}: {formatted_lines[-1]}", file=sys.stderr)
                rv = False
        else:
            if args.outdir is None:
                outdir = source.parent / f"{source.name}-py2many"

            successful, format_errors, failures = _process_dir(
                settings, source, outdir, args, env=env
            )
            rv = not (failures or format_errors)
        rv = 0 if rv is True else 1
        return rv
