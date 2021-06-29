import argparse
import filecmp
import logging
import os.path
import unittest
import sys

from distutils import spawn
from functools import lru_cache
from pathlib import Path
from subprocess import run
from unittest.mock import Mock
from unittest_expander import foreach, expand

from py2many.cli import (
    _create_cmd,
    _get_all_settings,
    _get_output_path,
    _relative_to_cwd,
    main,
)

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
    "cpp": [CXX, "-std=c++14", "-I", str(ROOT_DIR)]
    + (["-stdlib=libc++"] if CXX == "clang++" else [])
    + (["-o", "{exe}", "{filename}"] if sys.platform == "win32" else []),
    "dart": ["dart", "compile", "exe"],
    "go": ["go", "build"],
    "kotlin": ["kotlinc"],
    "nim": ["nim", "compile", "--nimcache:."],
    "rust": ["cargo", "script", "--build-only", "--debug"],
    "vlang": ["v", "-translated"],
}
INVOKER = {
    "dart": ["dart", "--enable-asserts"],
    "go": ["go", "run"],
    "julia": ["julia", "--compiled-modules=yes"],
    "kotlin": ["kscript"],
    "python": [sys.executable],
    "rust": ["cargo", "script"],
    "vlang": ["v", "-translated", "run"],
}

TEST_CASES = [
    item.stem
    for item in (TESTS_DIR / "cases").glob("*.py")
    if not item.stem.startswith("test_") and not item.stem in ["generator"]
]

CASE_ARGS = {
    "sys_argv": ("arg1",),
}
CASE_EXPECTED_EXITCODE = {
    "sys_exit": 1,
}

EXTENSION_TEST_CASES = [
    item.stem
    for item in (TESTS_DIR / "ext_cases").glob("*.py")
    if not item.stem.startswith("test_")
]

EXPECTED_LINT_FAILURES = []

EXPECTED_COMPILE_FAILURES = []

CARGO_TOML = [l.strip() for l in open(ROOT_DIR / "Cargo.toml").readlines()]

a_dot_out = "a.out"

logger = logging.Logger("test_cli")


def in_cargo_toml(case: str):
    return f'path = "tests/expected/{case}.rs"' in CARGO_TOML


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
    proc = run([sys.executable, str(case_filename), *main_args], capture_output=True)
    if exit_code:
        assert proc.returncode == exit_code
    elif proc.returncode:
        raise RuntimeError(f"Invalid {case_filename}:\n{proc.stdout}{proc.stderr}")
    return proc.stdout


def standardise_python(code):
    """Ignore differences in black output.

    black 21.6b0 outputs slightly different source between Python 3.8 amd 3.9
    For tuples, it is not consistent adding round brackets.
    And sometimes there are fewer blank newlines.
    """
    return (
        code.replace("(", "").replace(")", "").replace("\n\n", "\n").replace(".0j", "j")
    )


@expand
class CodeGeneratorTests(unittest.TestCase):
    maxDiff = None

    SHOW_ERRORS = SHOW_ERRORS
    KEEP_GENERATED = KEEP_GENERATED
    UPDATE_EXPECTED = UPDATE_EXPECTED
    LINT = os.environ.get("LINT", True)

    def setUp(self):
        os.makedirs(BUILD_DIR, exist_ok=True)
        os.chdir(BUILD_DIR)
        py2many.cli.CWD = BUILD_DIR

    @foreach(sorted(LANGS))
    @foreach(sorted(TEST_CASES))
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
            raise unittest.SkipTest(f"{expected_filename} not found")

        if settings.formatter:
            if not spawn.find_executable(settings.formatter[0]):
                raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = GENERATED_DIR / f"{case}{ext}"

        exe = get_exe_filename(case, ext)
        exe.unlink(missing_ok=True)

        is_script = has_main(case_filename)
        self.assertTrue(is_script)

        main_args = CASE_ARGS.get(case, tuple())
        expected_exit_code = CASE_EXPECTED_EXITCODE.get(case, 0)
        expected_output = get_python_case_output(
            case_filename, main_args, expected_exit_code
        )
        self.assertTrue(expected_output, "Test cases must print something")
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
                        if ext == ".py":
                            expected_case_contents = standardise_python(
                                expected_case_contents
                            )
                            generated_cleaned = standardise_python(generated)
                        self.assertEqual(expected_case_contents, generated_cleaned)
                        print("expected = generated")

            expect_failure = (
                not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_LINT_FAILURES
            )

            if not expect_failure:
                assert rv == 0, "formatting failed"
            elif rv:
                raise unittest.SkipTest("formatting failed")

            compiler = COMPILERS.get(lang)
            if compiler:
                if not spawn.find_executable(compiler[0]):
                    raise unittest.SkipTest(f"{compiler[0]} not available")
                expect_compile_failure = (
                    not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_COMPILE_FAILURES
                )
                if expect_compile_failure:
                    return
                cmd = _create_cmd(compiler, filename=case_output, exe=exe)
                print(f"Running {cmd} ...")
                proc = run(cmd, env=env, check=not expect_failure)

                if proc.returncode:
                    raise unittest.SkipTest(f"{case}{ext} doesnt compile")

                if self.UPDATE_EXPECTED or not os.path.exists(expected_filename):
                    with open(expected_filename, "w") as f:
                        f.write(generated)

            stdout = None
            if ext == ".cpp" and (BUILD_DIR / a_dot_out).exists():
                os.rename(BUILD_DIR / a_dot_out, exe)

            if INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if not spawn.find_executable(invoker[0]):
                    raise unittest.SkipTest(f"{invoker[0]} not available")
                cmd = _create_cmd(invoker, filename=case_output, exe=exe)
                cmd += main_args
                proc = run(
                    cmd,
                    env=env,
                    capture_output=True,
                )

                stdout = proc.stdout

                if expect_failure and expected_exit_code != proc.returncode:
                    raise unittest.SkipTest(f"Execution of {case}{ext} failed")
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

            self.assertTrue(stdout, "Invoked code produced no stdout")
            stdout = stdout.splitlines()
            self.assertEqual(expected_output, stdout)

            if settings.linter and self.LINT:
                if not spawn.find_executable(settings.linter[0]):
                    raise unittest.SkipTest(f"{settings.linter[0]} not available")
                if settings.ext == ".kt" and case_output.is_absolute():
                    # KtLint does not support absolute path in globs
                    case_output = _relative_to_cwd(case_output)
                linter = _create_cmd(settings.linter, case_output)
                if ext == ".cpp":
                    linter.append("-Wno-unused-variable")
                    if case == "coverage":
                        linter.append(
                            "-Wno-null-arithmetic"
                            if CXX == "clang++"
                            else "-Wno-pointer-arith"
                        )
                proc = run(linter, env=env)
                # golint is failing regularly due to exports without docs
                if proc.returncode and linter[0] == "golint":
                    expect_failure = True
                if proc.returncode and expect_failure:
                    raise unittest.SkipTest(f"{case}{ext} failed linter")
                self.assertFalse(proc.returncode)

                if expect_failure:
                    raise AssertionError(f"{case}{ext} passed unexpectedly")

        finally:
            if not self.KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
                exe.unlink(missing_ok=True)
        if settings.ext == ".rs":
            assert in_cargo_toml(case)

    @foreach(sorted(TEST_CASES))
    # This test name must be alpha before `test_generated` otherwise
    # KEEP_GENERATED does not work.
    def test_env_cxx_gcc(self, case):
        lang = "cpp"
        ext = ".cpp"
        expected_filename = TESTS_DIR / "expected" / f"{case}{ext}"
        if not os.path.exists(expected_filename):
            raise unittest.SkipTest(f"{expected_filename} not found")

        env = os.environ.copy()
        env["CXX"] = "g++-11" if sys.platform == "darwin" else "g++"
        env["CXXFLAGS"] = "-std=c++14 -Wall -Werror"

        if not spawn.find_executable(env["CXX"]):
            raise unittest.SkipTest(f"{env['CXX']} not available")

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        assert settings.linter[0].startswith("g++")

        if not spawn.find_executable("astyle"):
            raise unittest.SkipTest("astyle not available")

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
            raise unittest.SkipTest(f"Failed invoking {env['CXX']} or {linter}: {e}")
        finally:
            if not KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
            exe.unlink(missing_ok=True)

    def test_env_clang_format_style(self):
        lang = "cpp"
        env = {"CLANG_FORMAT_STYLE": "Google"}
        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        self.assertIn("-style=Google", settings.formatter)

    def test_arg_nim_indent(self):
        lang = "nim"
        settings = _get_all_settings(Mock(indent=2))[lang]
        self.assertIn("--indent:2", settings.formatter)

    @staticmethod
    def _rmdir_recursive(path: Path):
        try:
            for child in path.iterdir():
                if child.is_file():
                    child.unlink()
                else:
                    CodeGeneratorTests._rmdir_recursive(path)
            path.rmdir()
        except Exception as e:
            logger.debug(f"{repr(e)}: when removing dir: {path}")

    @foreach(sorted(EXTENSION_TEST_CASES))
    def test_ext(self, case):
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
                        self.assertEqual(f2.read(), generated)
                        print("expected = generated")

            if self.UPDATE_EXPECTED or not os.path.exists(expected_filename):
                with open(expected_filename, "w") as f:
                    f.write(generated)

        finally:
            if not self.KEEP_GENERATED:
                case_output.unlink(missing_ok=True)

    @foreach(sorted(LANGS))
    @foreach(["test1"])
    def test_directory(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        TEST_OUTPUT = f"{case}-{lang}-generated"
        EXPECTED_OUTPUT = f"{case}-{lang}-expected"
        case_dirname = ROOT_DIR / Path("tests/dir_cases") / case
        output_dir = ROOT_DIR / Path("tests/dir_cases") / TEST_OUTPUT
        expected_output_dir = ROOT_DIR / Path("tests/dir_cases") / EXPECTED_OUTPUT
        output_dir.mkdir(exist_ok=True)
        args = [
            f"--{lang}=1",
            str(case_dirname),
            "--outdir",
            str(output_dir),
        ]

        try:
            rv = main(args=args, env=env)
            if sys.platform == "win32" and rv != 0:
                raise unittest.SkipTest("transpiler failed")
            assert rv == 0
            output = filecmp.dircmp(expected_output_dir, output_dir)
            if sys.platform == "win32" and output.diff_files != []:
                raise unittest.SkipTest("directories don't match")
            assert output.diff_files == []
        finally:
            if not self.KEEP_GENERATED:
                self._rmdir_recursive(output_dir)


class TestPaths(unittest.TestCase):
    def test_output_path(self):
        base = Path(".")
        self.assertEqual(_get_output_path(Path("foo.py"), ".rs", base), Path("foo.rs"))
        self.assertEqual(
            _get_output_path(Path("dir/foo.py"), ".rs", base), Path("dir") / "foo.rs"
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

    CodeGeneratorTests.SHOW_ERRORS |= args.show_errors
    CodeGeneratorTests.KEEP_GENERATED |= args.keep_generated
    CodeGeneratorTests.UPDATE_EXPECTED |= args.update_expected
    CodeGeneratorTests.LINT |= args.lint

    rest = [sys.argv[0]] + rest
    unittest.main(argv=rest)
