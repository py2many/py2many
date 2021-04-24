import os.path
import unittest
import sys
from distutils import spawn
from pathlib import Path
from subprocess import run
from unittest.mock import Mock

from unittest_expander import foreach, expand

from py2many.cli import main, _get_all_settings

SHOW_ERRORS = os.environ.get("SHOW_ERRORS", False)

TESTS_DIR = Path(__file__).parent
ROOT_DIR = TESTS_DIR.parent

KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)
COMPILERS = {
    "cpp": ["clang++", "-std=c++14", "-I", str(ROOT_DIR), "-stdlib=libc++"],
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
COMPARABLE = [
    "bubble_sort",
    "comb_sort",
    "coverage",
    "fib",
    "global",
    "hello_world",
    "infer",
    "infer_ops",
    "lambda",
    "print",
    "rect",
    "int_enum",
    "str_enum",
]

EXPECTED_COMPILE_FAILURES = [
    "binit.jl",  # https://github.com/adsharma/py2many/issues/80
    "binit.nim",  # https://github.com/adsharma/py2many/issues/19
    "global.go",  # https://github.com/adsharma/py2many/issues/82
    "infer_ops.go",  # https://github.com/adsharma/py2many/issues/16
    "infer_ops.jl",  # https://github.com/adsharma/py2many/issues/78
    "infer_ops.kt",  # https://github.com/adsharma/py2many/issues/28
    "infer_ops.nim",  # https://github.com/adsharma/py2many/issues/16
    "infer_ops.rs",  # https://github.com/adsharma/py2many/issues/16
    "int_enum.cpp",
    "int_enum.dart",  # https://github.com/adsharma/py2many/issues/41
    "int_enum.go",  # https://github.com/adsharma/py2many/issues/75
    "int_enum.kt",  # https://github.com/adsharma/py2many/issues/28
    "int_enum.nim",  # https://github.com/adsharma/py2many/issues/76
    "lambda.go",  # https://github.com/adsharma/py2many/issues/15
    "lambda.kt",  # https://github.com/adsharma/py2many/issues/28
]


def has_main(filename):
    with open(filename) as f:
        lines = f.readlines()
    return bool(
        [line in line for line in lines if "def main" in line or "__main__" in line]
    )


@expand
class CodeGeneratorTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4))
    maxDiff = None

    def setUp(self):
        os.chdir(TESTS_DIR)

    @foreach(SETTINGS.keys())
    @foreach(TEST_CASES)
    def test_cli(self, case, lang):
        settings = self.SETTINGS[lang]
        ext = settings.ext
        if (
            not UPDATE_EXPECTED
            and not KEEP_GENERATED
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
        sys.argv = ["test", f"--{lang}=1", str(case_filename)]

        if case in COMPARABLE:
            expected_output = run(
                [sys.executable, str(case_filename)], capture_output=True, check=True
            ).stdout
            self.assertTrue(expected_output)
            expected_output = expected_output.splitlines()
        else:
            expected_output = None

        try:
            main()
            with open(f"cases/{case}{ext}") as actual:
                generated = actual.read()
                if os.path.exists(f"expected/{case}{ext}") and not UPDATE_EXPECTED:
                    with open(f"expected/{case}{ext}") as f2:
                        self.assertEqual(f2.read(), generated)
                        print("expected = generated")

            if ext in [".cpp", ".dart"] and not is_script:
                # See https://github.com/adsharma/py2many/issues/25
                raise unittest.SkipTest(f"{case}{ext} doesnt have a main")

            expect_failure = (
                not SHOW_ERRORS and f"{case}{ext}" in EXPECTED_COMPILE_FAILURES
            )
            compiler = COMPILERS[lang]
            if ext == ".rs" and not is_script:
                compiler = ["rust-script"]
            if compiler:
                if not spawn.find_executable(compiler[0]):
                    raise unittest.SkipTest(f"{compiler[0]} not available")
                proc = run([*compiler, f"cases/{case}{ext}"], check=not expect_failure)

                assert not expect_failure or proc.returncode != 0
                if proc.returncode:
                    raise unittest.SkipTest(f"{case}{ext} doesnt compile")

                if UPDATE_EXPECTED or not os.path.exists(f"expected/{case}{ext}"):
                    with open(f"expected/{case}{ext}", "w") as f:
                        f.write(generated)

            stdout = None
            if exe.exists() and os.access(exe, os.X_OK):
                stdout = run([exe], capture_output=True, check=True).stdout
            elif ext in [".go", ".rs", ".kt"] and not is_script:
                raise unittest.SkipTest(f"{case}{ext} needs main() to be invoked")
            elif INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if not spawn.find_executable(invoker[0]):
                    raise unittest.SkipTest(f"{invoker[0]} not available")
                proc = run(
                    [*invoker, case_output],
                    capture_output=True,
                    check=not expect_failure,
                )

                stdout = proc.stdout

                assert not expect_failure or proc.returncode != 0
                if proc.returncode:
                    raise unittest.SkipTest(f"{case}{ext} doesnt compile")
            else:
                raise RuntimeError("Compiled output not detected")

            if expected_output and stdout:
                stdout = stdout.splitlines()
                self.assertEqual(expected_output, stdout)

        finally:
            if not KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
            exe.unlink(missing_ok=True)


if __name__ == "__main__":
    unittest.main()
