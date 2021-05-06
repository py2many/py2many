import argparse
import os.path
import unittest
import sys

from distutils import spawn
from pathlib import Path
from subprocess import run
from unittest.mock import Mock
from unittest_expander import foreach, expand

from py2many.cli import main, _create_cmd, _get_all_settings

TESTS_DIR = Path(__file__).parent.absolute()
ROOT_DIR = TESTS_DIR.parent

KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)
CXX = os.environ.get("CXX", "clang++")
ENV = {
    "cpp": {
        "CLANG_FORMAT_STYLE": "LLVM",
    },
    "rust": {
        "RUSTFLAGS": "--deny warnings",
    },
}
COMPILERS = {
    "cpp": [CXX, "-std=c++14", "-I", str(ROOT_DIR)]
    + (["-stdlib=libc++"] if CXX == "clang++" else []),
    "dart": ["dart", "compile", "exe"],
    "go": ["go", "build"],
    "julia": ["julia", "--compiled-modules=yes"],
    "kotlin": ["kotlinc"],
    "nim": ["nim", "compile", "--nimcache:."],
    "rust": ["cargo", "script", "--build-only", "--debug"],
}
INVOKER = {
    "go": ["go", "run"],
    "julia": ["julia", "--compiled-modules=yes"],
    "kotlin": ["kscript"],
    "rust": ["cargo", "script"],
}

TEST_CASES = [
    item.stem
    for item in (TESTS_DIR / "cases").glob("*.py")
    if not item.stem.startswith("test_")
]

EXPECTED_LINT_FAILURES = ["int_enum.go", "rect.go", "str_enum.go"]

EXPECTED_COMPILE_FAILURES = []


def has_main(filename):
    with open(filename) as f:
        lines = f.readlines()
    return bool(
        [line in line for line in lines if "def main" in line or "__main__" in line]
    )


@expand
class CodeGeneratorTests(unittest.TestCase):
    LANGS = list(_get_all_settings(Mock(indent=4)).keys())
    maxDiff = None

    SHOW_ERRORS = os.environ.get("SHOW_ERRORS", False)
    KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
    UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)
    LINT = os.environ.get("LINT", True)

    def setUp(self):
        os.chdir(TESTS_DIR)

    @foreach(sorted(LANGS))
    @foreach(sorted(TEST_CASES))
    def test_generated(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        ext = settings.ext
        if (
            not self.UPDATE_EXPECTED
            and not self.KEEP_GENERATED
            and not os.path.exists(f"expected/{case}{ext}")
        ):
            raise unittest.SkipTest(f"expected/{case}{ext} not found")

        if settings.formatter:
            if not spawn.find_executable(settings.formatter[0]):
                raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        if ext == ".kt":
            class_name = str(case.title()) + "Kt"
            exe = TESTS_DIR / (class_name + ".class")
        elif ext == ".cpp":
            exe = TESTS_DIR / "a.out"
        elif ext == ".dart" or (ext == ".nim" and sys.platform == "win32"):
            exe = TESTS_DIR / "cases" / f"{case}.exe"
        else:
            exe = TESTS_DIR / "cases" / f"{case}"
        exe.unlink(missing_ok=True)

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = TESTS_DIR / "cases" / f"{case}{ext}"
        is_script = has_main(case_filename)
        self.assertTrue(is_script)

        proc = run([sys.executable, str(case_filename)], capture_output=True)
        expected_output = proc.stdout
        if proc.returncode:
            raise RuntimeError(
                f"Invalid cases/{case}.py:\n{expected_output}{proc.stderr}"
            )
        self.assertTrue(expected_output, "Test cases must print something")
        expected_output = expected_output.splitlines()

        args = [f"--{lang}=1", str(case_filename)]

        try:
            rv = main(args=args, env=env)
            with open(f"cases/{case}{ext}") as actual:
                generated = actual.read()
                if os.path.exists(f"expected/{case}{ext}") and not self.UPDATE_EXPECTED:
                    with open(f"expected/{case}{ext}") as f2:
                        self.assertEqual(f2.read(), generated)
                        print("expected = generated")

            expect_failure = (
                not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_LINT_FAILURES
            )

            if not expect_failure:
                assert rv, "formatting failed"
            elif not rv:
                raise unittest.SkipTest("formatting failed")

            compiler = COMPILERS[lang]
            if compiler:
                if not spawn.find_executable(compiler[0]):
                    raise unittest.SkipTest(f"{compiler[0]} not available")
                expect_compile_failure = (
                    not self.SHOW_ERRORS and f"{case}{ext}" in EXPECTED_COMPILE_FAILURES
                )
                if expect_compile_failure:
                    return
                proc = run(
                    [*compiler, f"cases/{case}{ext}"], env=env, check=not expect_failure
                )

                if proc.returncode:
                    raise unittest.SkipTest(f"{case}{ext} doesnt compile")

                if self.UPDATE_EXPECTED or not os.path.exists(f"expected/{case}{ext}"):
                    with open(f"expected/{case}{ext}", "w") as f:
                        f.write(generated)

            stdout = None
            if exe.exists() and os.access(exe, os.X_OK):
                stdout = run([exe], env=env, capture_output=True, check=True).stdout

            elif INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if not spawn.find_executable(invoker[0]):
                    raise unittest.SkipTest(f"{invoker[0]} not available")
                proc = run(
                    [*invoker, case_output],
                    env=env,
                    capture_output=True,
                    check=not expect_failure,
                )

                stdout = proc.stdout

                if proc.returncode:
                    raise unittest.SkipTest(f"Execution of {case}{ext} failed")
            else:
                raise RuntimeError("Compiled output not detected")

            if expected_output and stdout:
                stdout = stdout.splitlines()
                self.assertEqual(expected_output, stdout)

                if settings.linter and self.LINT:
                    if not spawn.find_executable(settings.linter[0]):
                        raise unittest.SkipTest(f"{settings.linter[0]} not available")
                    if settings.ext == ".kt" and case_output.is_absolute():
                        # KtLint does not support absolute path in globs
                        case_output = case_output.relative_to(Path.cwd())
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

    @foreach(sorted(TEST_CASES))
    # This test name must be alpha before `test_generated` otherwise
    # KEEP_GENERATED does not work.
    def test_env_cxx_gcc(self, case):
        lang = "cpp"
        ext = ".cpp"
        if not os.path.exists(f"expected/{case}{ext}"):
            raise unittest.SkipTest(f"expected/{case}{ext} not found")

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

        exe = TESTS_DIR / "a.out"
        exe.unlink(missing_ok=True)

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = TESTS_DIR / "cases" / f"{case}{ext}"

        args = [f"--{lang}=1", str(case_filename)]

        linter = _create_cmd(settings.linter, case_output)

        try:
            rv = main(args=args, env=env)
            assert rv

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
        env = {
            "CLANG_FORMAT_STYLE": "Google",
        }
        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        self.assertIn("-style=Google", settings.formatter)

    def test_arg_nim_indent(self):
        lang = "nim"
        settings = _get_all_settings(Mock(indent=2))[lang]
        self.assertIn("--indent:2", settings.formatter)


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
