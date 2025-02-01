import argparse
import logging
import os.path
import platform
import sys
from functools import lru_cache
from itertools import product
from pathlib import Path
from subprocess import run
from unittest.mock import Mock

import pytest

from py2many.cli import (
    _create_cmd,
    _get_all_settings,
    _get_output_path,
    _relative_to_cwd,
    main,
)
from py2many.process_helpers import find_executable

try:
    from py2many.pycpp import _conan_include_args
except ImportError:
    from pycpp import _conan_include_args

import py2many.cli

TESTS_DIR = Path(__file__).parent.absolute()
ROOT_DIR = TESTS_DIR.parent
BUILD_DIR = TESTS_DIR / "build"
GENERATED_DIR = BUILD_DIR

KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
SHOW_ERRORS = os.environ.get("SHOW_ERRORS", False)
UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)

CXX = os.environ.get("CXX", "clang++")
LANGS = list(_get_all_settings(Mock(indent=4)).keys())
ENV = {
    "cpp": {"CLANG_FORMAT_STYLE": "Google"},
    "rust": {"RUSTFLAGS": "--deny warnings"},
}
COMPILERS = {
    "cpp": [CXX, "-std=c++17", "-I", str(ROOT_DIR)]
    + _conan_include_args()
    + (["-stdlib=libc++"] if CXX.startswith("clang++") else [])
    + (["-o", "{exe}", "{filename}"] if sys.platform == "win32" else []),
    "dlang": ["dmd"],
    "dart": ["dart", "compile", "exe"],
    "go": ["go", "build"],
    "nim": ["nim", "compile", "--nimcache:."],
    "rust": [
        "../../scripts/rust-runner.sh",
        "compile",
    ],
    "vlang": ["v"],
    "mojo": ["mojo", "build"],
}

INVOKER = {
    "dart": ["dart", "--enable-asserts"],
    "dlang": ["dmd", "-run"],
    "go": ["go", "run"],
    "julia": ["julia", "--compiled-modules=yes"],
    "python": [sys.executable],
    "rust": [
        "../../scripts/rust-runner.sh",
        "run",
    ],
    "smt": ["z3", "-smt2"],
    "vlang": ["v", "run"],
    "mojo": ["mojo"],
}

# kscript requires a KOTLIN_HOME.
# If it isnt present, set compilation using kotlinc which should also be missing,
# which will cause Kotlin cases to be skipped.
if os.getenv("KOTLIN_HOME"):
    INVOKER["kotlin"] = [
        "jgo",
        "--log-level=DEBUG",
        "--additional-endpoints",
        "commons-cli:commons-cli",
        "commons-codec:commons-codec",
        "io.github.kscripting:shell",
        "io.github.kscripting:kscript:io.github.kscripting.kscript.KscriptKt",
        platform.system().lower(),
    ]
else:
    COMPILERS["kotlin"] = ["kotlinc"]

TEST_CASES = [item.stem for item in (TESTS_DIR / "cases").glob("*.py")]
TEST_PARAMS = [(case, lang) for case, lang in product(TEST_CASES, LANGS)]

CASE_ARGS = {"sys_argv": ("arg1",)}
CASE_EXPECTED_EXITCODE = {"sys_exit": 1}

EXTENSION_TEST_CASES = [
    item.stem
    for item in (TESTS_DIR / "ext_cases").glob("*.py")
    if not item.stem.startswith("test_")
]

EXPECTED_LINT_FAILURES = []

EXPECTED_COMPILE_FAILURES = []

a_dot_out = "a.out"

logger = logging.Logger("test_cli")


def has_main_lines(lines):
    return any("def main" in line or "__main__" in line for line in lines)


def has_main(filename):
    with open(filename) as f:
        lines = f.readlines()
    return has_main_lines(lines)


def get_exe_filename(case, ext):
    if ext == ".kt":
        class_name = str(case.title()) + "Kt"
        exe = BUILD_DIR / (class_name + ".class")
    elif ext in [".dart", ".cpp"] or (ext == ".nim" and sys.platform == "win32"):
        exe = GENERATED_DIR / f"{case}.exe"
    else:
        exe = GENERATED_DIR / f"{case}"
    return exe


@lru_cache()
def get_python_case_output(case_filename, main_args, exit_code):
    proc = run(
        [sys.executable, str(case_filename), *main_args],
        capture_output=True,
        check=False,
    )
    if exit_code:
        assert proc.returncode == exit_code
    elif proc.returncode:
        raise RuntimeError(f"Invalid {case_filename}:\n{proc.stdout}{proc.stderr}")
    return proc.stdout


def standardise_python(code):
    """Ignore differences in black output.

    black outputs slightly different source between Python versions.
    For tuples, it is not consistent adding round brackets.
    And sometimes there are fewer blank newlines.
    """
    return (
        code.replace("(", "").replace(")", "").replace("\n\n", "\n").replace(".0j", "j")
    )


def standardise_eol(code):
    """Ignore differences in EOLs."""
    if sys.platform != "win32":
        return code
    return code.replace("\r\n", "\n").replace("\n\n", "\n")


def is_declarative(ext):
    """The scripts in these languages can't be run. They declare some
    constraints that could be verified later in the COMPILER. No INVOKER."""
    return ext in {".smt"}


class TestCodeGenerator:
    maxDiff = None

    SHOW_ERRORS = SHOW_ERRORS
    KEEP_GENERATED = KEEP_GENERATED
    UPDATE_EXPECTED = UPDATE_EXPECTED
    LINT = os.environ.get("LINT", True)

    @classmethod
    def setup_class(cls):
        os.makedirs(BUILD_DIR, exist_ok=True)
        os.chdir(BUILD_DIR)
        py2many.cli.CWD = BUILD_DIR

    @pytest.mark.parametrize("case,lang", TEST_PARAMS)
    def test_generated(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        ext = settings.ext
        expected_filename = TESTS_DIR / "expected" / f"{case}{ext}"

        if (
            not self.UPDATE_EXPECTED
            and not self.KEEP_GENERATED
            and not os.path.exists(expected_filename)
        ):
            raise pytest.skip(f"{expected_filename} not found")

        if settings.formatter:
            if not find_executable(settings.formatter[0]):
                raise pytest.skip(f"{settings.formatter[0]} not available")

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = GENERATED_DIR / f"{case}{ext}"

        exe = get_exe_filename(case, ext)
        exe.unlink(missing_ok=True)

        is_script = has_main(case_filename)
        if not is_script and not is_declarative(ext):
            raise pytest.skip(f"{case} is declarative, not suitable for {lang}")

        if not is_declarative(ext):
            main_args = CASE_ARGS.get(case, tuple())
            expected_exit_code = CASE_EXPECTED_EXITCODE.get(case, 0)
            expected_output = get_python_case_output(
                case_filename, main_args, expected_exit_code
            )
            assert expected_output, "Test cases must print something"
            expected_output = expected_output.splitlines()

        args = [
            f"--{lang}=1",
            "--comment-unsupported",
            str(case_filename),
            "--outdir",
            str(GENERATED_DIR),
        ]

        try:
            rv = main(args=args, env=env)
            with open(case_output) as actual:
                generated = actual.read()
                if os.path.exists(expected_filename) and not self.UPDATE_EXPECTED:
                    with open(expected_filename) as f2:
                        expected_case_contents = f2.read()
                        generated_cleaned = generated
                        # Only require equivalent output on latest Python version
                        if ext == ".py" and sys.version_info < (3, 12, 0):
                            expected_case_contents = standardise_python(
                                expected_case_contents
                            )
                            generated_cleaned = standardise_python(generated)
                        assert expected_case_contents == generated_cleaned
                        print("expected = generated")

            expect_failure = (
                not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_LINT_FAILURES
            )

            if not expect_failure:
                assert rv == 0, "formatting failed"
            elif rv:
                raise pytest.skip("formatting failed")

            compiler = COMPILERS.get(lang)
            if compiler:
                if not find_executable(compiler[0]):
                    raise pytest.skip(f"{compiler[0]} not available")
                expect_compile_failure = (
                    not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_COMPILE_FAILURES
                )
                if expect_compile_failure:
                    return
                cmd = _create_cmd(compiler, filename=case_output, exe=exe)
                print(f"Compiling {cmd} ...")
                proc = run(cmd, env=env, check=False)

                if proc.returncode and not expect_failure:
                    raise pytest.skip(f"{case}{ext} doesnt compile")

                if self.UPDATE_EXPECTED or not os.path.exists(expected_filename):
                    with open(expected_filename, "w") as f:
                        f.write(generated)

            if is_declarative(ext):
                return

            stdout = None
            if ext == ".cpp" and (BUILD_DIR / a_dot_out).exists():
                os.rename(BUILD_DIR / a_dot_out, exe)

            if INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if os.path.exists(invoker[0]):
                    pass
                elif not find_executable(invoker[0]):
                    raise pytest.skip(f"{invoker[0]} not available")
                cmd = _create_cmd(invoker, filename=case_output, exe=exe)
                cmd += main_args
                print(f"Invoking {cmd} ...")
                proc = run(cmd, env=env, capture_output=True)

                stdout = proc.stdout

                if expect_failure and expected_exit_code != proc.returncode:
                    raise pytest.skip(f"Execution of {case}{ext} failed")
                assert (
                    expected_exit_code == proc.returncode
                ), f"Execution of {case}{ext} failed:\n{stdout}{proc.stderr}"

                if self.UPDATE_EXPECTED or not os.path.exists(expected_filename):
                    with open(expected_filename, "w") as f:
                        f.write(generated)
            elif exe.exists() and os.access(exe, os.X_OK):
                cmd = [exe, *main_args]
                print(f"Running {cmd} ...")
                proc = run(cmd, env=env, capture_output=True)
                assert expected_exit_code == proc.returncode

                stdout = proc.stdout
            else:
                raise RuntimeError(f"Compiled output {exe} not detected")

            assert stdout, "Invoked code produced no stdout"
            stdout = stdout.splitlines()
            assert expected_output == stdout

            if settings.linter and self.LINT:
                if not find_executable(settings.linter[0]):
                    raise pytest.skip(f"{settings.linter[0]} not available")
                if settings.ext == ".kt" and case_output.is_absolute():
                    # KtLint does not support absolute path in globs
                    case_output = _relative_to_cwd(case_output)
                linter = _create_cmd(settings.linter, case_output)
                print(f"Running linter {linter} ...")
                if ext == ".cpp":
                    linter.append("-Wno-unused-variable")
                    if case == "coverage":
                        linter.append(
                            "-Wno-null-arithmetic"
                            if CXX.startswith("clang++")
                            else "-Wno-pointer-arith"
                        )
                proc = run(linter, env=env)
                # golint is failing regularly due to exports without docs
                if proc.returncode and linter[0] == "golint":
                    expect_failure = True
                if proc.returncode and expect_failure:
                    raise pytest.skip(f"{case}{ext} failed linter")
                assert not proc.returncode

                if expect_failure:
                    raise AssertionError(f"{case}{ext} passed unexpectedly")

        finally:
            if not self.KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
                exe.unlink(missing_ok=True)

    @pytest.mark.parametrize("case", TEST_CASES)
    # This test name must be alpha before `test_generated` otherwise
    # KEEP_GENERATED does not work.
    def test_env_cxx_gcc(self, case):
        lang = "cpp"
        ext = ".cpp"
        expected_filename = TESTS_DIR / "expected" / f"{case}{ext}"
        if not os.path.exists(expected_filename):
            raise pytest.skip(f"{expected_filename} not found")

        env = os.environ.copy()
        env["CXX"] = "g++-11" if sys.platform == "darwin" else "g++"
        env["CXXFLAGS"] = "-std=c++17 -Wall -Werror"

        if not find_executable(env["CXX"]):
            raise pytest.skip(f"{env['CXX']} not available")

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        assert settings.linter[0].startswith("g++")

        if not find_executable("astyle"):
            raise pytest.skip("astyle not available")

        settings.formatter = ["astyle"]

        exe = BUILD_DIR / a_dot_out
        exe.unlink(missing_ok=True)

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = GENERATED_DIR / f"{case}{ext}"

        args = [
            f"--{lang}=1",
            "--comment-unsupported",
            str(case_filename),
            "--outdir",
            str(GENERATED_DIR),
        ]

        linter = _create_cmd(settings.linter, case_output)

        try:
            rv = main(args=args, env=env)
            assert rv == 0

            linter.append("-Wno-unused-variable")
            if case == "coverage":
                linter.append("-Wno-pointer-arith")
            proc = run(linter, env=env)
            assert not proc.returncode
        except FileNotFoundError as e:
            raise pytest.skip(f"Failed invoking {env['CXX']} or {linter}: {e}")
        finally:
            if not KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
            exe.unlink(missing_ok=True)

    @staticmethod
    def _rmdir_recursive(path: Path):
        try:
            for child in path.iterdir():
                if child.is_file():
                    child.unlink()
                else:
                    TestCodeGenerator._rmdir_recursive(path)
            path.rmdir()
        except Exception as e:
            logger.debug(f"{repr(e)}: when removing dir: {path}")

    @pytest.mark.parametrize("case", EXTENSION_TEST_CASES)
    def test_rust_ext(self, case):
        lang = "rust"
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=2))[lang]
        ext = settings.ext
        expected_filename = TESTS_DIR / "ext_expected" / f"{case}{ext}"
        case_filename = TESTS_DIR / "ext_cases" / f"{case}.py"
        case_output = GENERATED_DIR / f"{case}{ext}"

        args = [
            "--rust=1",
            "--extension",
            str(case_filename),
            "--outdir",
            str(GENERATED_DIR),
        ]
        sys.argv += args

        try:
            main(args=args, env=env)
            with open(case_output) as actual:
                generated = actual.read()
                if os.path.exists(expected_filename) and not self.UPDATE_EXPECTED:
                    with open(expected_filename) as f2:
                        assert f2.read() == generated
                        print("expected = generated")

            if self.UPDATE_EXPECTED or not os.path.exists(expected_filename):
                with open(expected_filename, "w") as f:
                    f.write(generated)

        finally:
            if not self.KEEP_GENERATED:
                case_output.unlink(missing_ok=True)

    @pytest.mark.parametrize("case, lang", product(["test1"], LANGS))
    def test_directory(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        if settings.formatter:
            if not find_executable(settings.formatter[0]):
                raise pytest.skip(f"{settings.formatter[0]} not available")

        ext = settings.ext
        TEST_OUTPUT = f"{case}-{lang}-generated"
        EXPECTED_OUTPUT = f"{case}-{lang}-expected"
        case_dirname = ROOT_DIR / Path("tests/dir_cases") / case
        output_dir = ROOT_DIR / Path("tests/dir_cases") / TEST_OUTPUT
        expected_output_dir = ROOT_DIR / Path("tests/dir_cases") / EXPECTED_OUTPUT
        output_dir.mkdir(exist_ok=True)
        args = [
            f"--{lang}=1",
            str(case_dirname),
            "--project=0",
            "--outdir",
            str(output_dir),
        ]

        try:
            rv = main(args=args, env=env)
            assert rv == 0

            filenames = list(expected_output_dir.glob(f"*{ext}"))
            assert filenames
            for expected_filename in filenames:
                output_filename = output_dir / (expected_filename.stem + ext)
                print(f"Checking {expected_filename} vs {output_filename}")
                with open(expected_filename) as fh:
                    expected_contents = fh.read()
                assert standardise_eol(expected_contents)

                with open(output_filename) as fh:
                    generated_contents = fh.read()
                assert standardise_eol(generated_contents)

                assert standardise_eol(generated_contents) == standardise_eol(
                    expected_contents
                )
        finally:
            if not self.KEEP_GENERATED:
                self._rmdir_recursive(output_dir)

    def test_output_path(self):
        base = Path(".")
        assert _get_output_path(Path("foo.py"), ".rs", base) == Path("foo.rs")
        assert (
            _get_output_path(Path("dir/foo.py"), ".rs", base) == Path("dir") / "foo.rs"
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lint", type=bool, default=False, help="Lint generated code")
    parser.add_argument(
        "--show-errors", type=bool, default=False, help="Show compile errors"
    )
    parser.add_argument(
        "--keep-generated",
        type=bool,
        default=False,
        help="Keep generated code for debug",
    )
    parser.add_argument(
        "--update-expected", type=bool, default=False, help="Update tests/expected"
    )
    args, rest = parser.parse_known_args()

    TestCodeGenerator.SHOW_ERRORS |= args.show_errors
    TestCodeGenerator.KEEP_GENERATED |= args.keep_generated
    TestCodeGenerator.UPDATE_EXPECTED |= args.update_expected
    TestCodeGenerator.LINT |= args.lint

    rest = [sys.argv[0]] + rest
    pytest.main(rest)
