import os.path
import unittest
import sys
from distutils import spawn
from pathlib import Path
from subprocess import run
from unittest.mock import Mock

from unittest_expander import foreach, expand

from py2many.cli import main, _get_all_settings

KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)
COMPILERS = {
    # cpp is disabled due to https://github.com/adsharma/py2many/issues/24
    # "cpp": ["clang", "-std=c++14"],
    "dart": ["dart"],
    "go": ["go", "tool", "compile"],
    "julia": ["julia"],
    "kotlin": ["kotlinc"],
    "nim": ["nim", "compile", "--nimcache:."],
    "rust": ["rust-script"],
}
EXPECTED_COMPILE_FAILURES = [
    "binit.go",  # https://github.com/adsharma/py2many/issues/23
    "binit.kt",  # https://github.com/adsharma/py2many/issues/28
    "binit.nim",  # https://github.com/adsharma/py2many/issues/19
    "binit.rs",  # https://github.com/adsharma/py2many/issues/19
    "infer.go",  # https://github.com/adsharma/py2many/issues/23
    "infer.kt",  # https://github.com/adsharma/py2many/issues/28
    "infer_ops.go",  # https://github.com/adsharma/py2many/issues/16
    "infer_ops.kt",  # https://github.com/adsharma/py2many/issues/28
    "infer_ops.nim",  # https://github.com/adsharma/py2many/issues/16
    "infer_ops.rs",  # https://github.com/adsharma/py2many/issues/16
    "int_enum.jl",  # https://github.com/adsharma/py2many/issues/26
    "int_enum.kt",  # https://github.com/adsharma/py2many/issues/28
    "lambda.dart",  # https://github.com/adsharma/py2many/issues/34
    "lambda.go",  # https://github.com/adsharma/py2many/issues/15
    "lambda.kt",  # https://github.com/adsharma/py2many/issues/28
    "lambda.nim",  # https://github.com/adsharma/py2many/issues/27
    "lambda.rs",  # https://github.com/adsharma/py2many/issues/15
    "str_enum.jl",  # https://github.com/adsharma/py2many/issues/26
]


@expand
class CodeGeneratorTests(unittest.TestCase):
    TESTS_DIR = Path(__file__).parent
    TEST_CASES = [
        item.stem
        for item in (TESTS_DIR / "cases").glob("*.py")
        if not item.stem.startswith("test_")
    ]
    SETTINGS = _get_all_settings(Mock(indent=4))
    maxDiff = None

    def setUp(self):
        os.chdir(self.TESTS_DIR)

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
            formatter = settings.formatter.split()[0]
            if not spawn.find_executable(formatter):
                raise unittest.SkipTest(f"{formatter} not available")
        sys.argv = ["test", f"--{lang}=1", f"cases/{case}.py"]
        try:
            main()
            with open(f"cases/{case}{ext}") as actual:
                generated = actual.read()
                if os.path.exists(f"expected/{case}{ext}") and not UPDATE_EXPECTED:
                    with open(f"expected/{case}{ext}") as f2:
                        self.assertEqual(f2.read(), generated)

            if (
                ext == ".dart"
                and "void main() {" not in generated
                and "main() {" not in generated
            ):
                # See https://github.com/adsharma/py2many/issues/25
                raise unittest.SkipTest(f"{case}{ext} doesnt have a main")

            expect_failure = f"{case}{ext}" in EXPECTED_COMPILE_FAILURES
            compiler = COMPILERS.get(lang)
            if compiler and spawn.find_executable(compiler[0]):
                proc = run([*compiler, f"cases/{case}{ext}"], check=not expect_failure)

                assert not expect_failure or proc.returncode != 0
                if proc.returncode:
                    raise unittest.SkipTest(f"{case}{ext} doesnt compile")

                if UPDATE_EXPECTED or not os.path.exists(f"expected/{case}{ext}"):
                    with open(f"expected/{case}{ext}", "w") as f:
                        f.write(generated)
        finally:
            try:
                if not KEEP_GENERATED:
                    os.unlink(f"cases/{case}{ext}")
            except FileNotFoundError:
                pass


if __name__ == "__main__":
    unittest.main()
