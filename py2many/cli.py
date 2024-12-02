import argparse
import ast
import os
import sys
import tempfile
from functools import lru_cache
from pathlib import Path
from subprocess import run
from typing import List, Optional, Set, Tuple

from .analysis import add_imports
from .annotation_transformer import add_annotation_flags
from .context import add_assignment_context, add_list_calls, add_variable_context
from .exceptions import AstErrorBase
from .inference import infer_types, infer_types_typpete
from .language import LanguageSettings
from .mutability_transformer import detect_mutable_vars
from .nesting_transformer import detect_nesting_levels
from .raises_transformer import detect_raises
from .registry import ALL_SETTINGS, FAKE_ARGS, _get_all_settings
from .rewriters import (
    ComplexDestructuringRewriter,
    DocStringToCommentRewriter,
    FStringJoinRewriter,
    IgnoredAssignRewriter,
    LoopElseRewriter,
    PrintBoolRewriter,
    PythonMainRewriter,
    StrStrRewriter,
    UnpackScopeRewriter,
    WithToBlockTransformer,
)
from .scope import add_scope_context
from .toposort_modules import toposort
from .version import __version__

PY2MANY_DIR = Path(__file__).parent
ROOT_DIR = PY2MANY_DIR.parent
STDIN = "-"
STDOUT = "-"
CWD = Path.cwd()


def core_transformers(tree, trees, args):
    add_variable_context(tree, trees)
    add_scope_context(tree)
    add_assignment_context(tree)
    add_list_calls(tree)
    detect_mutable_vars(tree)
    detect_nesting_levels(tree)
    detect_raises(tree)
    add_annotation_flags(tree)
    infer_meta = (
        infer_types_typpete(tree) if args and args.typpete else infer_types(tree)
    )
    add_imports(tree)
    return tree, infer_meta


def _transpile(
    filenames: List[Path],
    sources: List[str],
    settings: LanguageSettings,
    args: Optional[argparse.Namespace] = None,
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
    if settings.ext != ".py":
        generic_post_rewriters.append(LoopElseRewriter(language))

    rewriters = generic_rewriters + rewriters
    post_rewriters = generic_post_rewriters + post_rewriters
    outputs = {}
    successful = []
    for filename, tree in zip(topo_filenames, trees):
        try:
            output = _transpile_one(
                trees, tree, transpiler, rewriters, transformers, post_rewriters, args
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


def _transpile_one(
    trees, tree, transpiler, rewriters, transformers, post_rewriters, args
):
    # This is very basic and needs to be run before and after
    # rewrites. Revisit if running it twice becomes a perf issue
    add_scope_context(tree)
    # Language specific rewriters
    for rewriter in rewriters:
        tree = rewriter.visit(tree)
    # Language independent core transformers
    tree, infer_meta = core_transformers(tree, trees, args)
    # Language specific transformers
    for tx in transformers:
        tx(tree)
    # Language specific rewriters that depend on previous steps
    for rewriter in post_rewriters:
        tree = rewriter.visit(tree)
    # Rerun core transformers
    tree, infer_meta = core_transformers(tree, trees, args)
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
        output = _process_one_data(sys.stdin.read(), Path("test.py"), settings)
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
    with open(filename) as f:
        source_data = f.read()
    dunder_init = filename.stem == "__init__"
    if dunder_init and not source_data:
        print("Detected empty __init__; skipping")
        return True
    result = _transpile([filename], [source_data], settings, args)
    with open(output_path, "wb") as f:
        f.write(result[0][0].encode("utf-8"))

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
        if settings.ignore_formatter_errors:
            return True
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
        filenames, source_data, settings, _suppress_exceptions=_suppress_exceptions
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


def _process_dir(
    settings, source, outdir, project, env=None, _suppress_exceptions=Exception
):
    print(f"Transpiling whole directory to {outdir}:")

    if settings.create_project is not None and project:
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
    LANGS = _get_all_settings(FAKE_ARGS)
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
        "--no-strict",
        dest="strict",
        default=True,
        action="store_false",
        help="Skip over unsupported constructs and generate some code",
    )
    parser.add_argument(
        "--ignore-formatter-errors",
        dest="ignore_formatter_errors",
        default=False,
        action="store_true",
        help="Ignore formatter error if its not installed",
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
        "--version",
        action="store_true",
        default=False,
        help="Display version number",
    )
    parser.add_argument(
        "--project", default=True, help="Create a project when using directory mode"
    )
    args, rest = parser.parse_known_args(args=args)

    if args.version:
        print(__version__)
        return 0

    # Validation of the args
    if args.extension and not args.rust:
        print("extension supported only with rust via pyo3")
        return -1

    settings_func = ALL_SETTINGS["cpp"]
    for lang, func in ALL_SETTINGS.items():
        arg = getattr(args, lang)
        if arg:
            settings_func = func
            break
    settings = settings_func(args, env=env)

    if args.comment_unsupported:
        print("Wrapping unimplemented in comments")
        settings.transpiler.set_continue_on_unimplemented()

    if not args.strict:
        print("Warning: some code may be experimental and incorrect")
        settings.transpiler.set_continue_on_unimplemented()

    settings.ignore_formatter_errors = args.ignore_formatter_errors

    for filename in rest:
        source = Path(filename)
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
                settings, source, outdir, args.project, env=env
            )
            rv = not (failures or format_errors)
        rv = 0 if rv is True else 1
        return rv
