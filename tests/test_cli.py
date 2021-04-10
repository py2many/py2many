import os.path
import unittest
import sys
from distutils import spawn
from pathlib import Path
from unittest.mock import Mock

from unittest_expander import foreach, expand

from py2many.cli import main, _get_all_settings


@expand
class CodeGeneratorTests(unittest.TestCase):
    TEST_CASES = [
        "fib",
        "rect",
        "infer",
        "infer-ops",
        "binit",
        "lambda",
        "int_enum",
        "str_enum",
        "print",
    ]
    TESTS_DIR = Path(__file__).parent
    SETTINGS = _get_all_settings(Mock(indent=4))

    def setUp(self):
        os.chdir(self.TESTS_DIR)

    @foreach(SETTINGS.keys())
    @foreach(TEST_CASES)
    def test_cli(self, case, lang):
        settings = self.SETTINGS[lang]
        ext = settings.ext
        if not os.path.exists(f"expected/{case}{ext}"):
            raise unittest.SkipTest(f"expected/{case}{ext} not found")
        formatter = settings.formatter.split()[0]
        if not spawn.find_executable(formatter):
            raise unittest.SkipTest(f"{formatter} not available")
        sys.argv = ["test", f"--{lang}=1", f"cases/{case}.py"]
        try:
            main()
            with open(f"expected/{case}{ext}") as f2:
                with open(f"cases/{case}{ext}") as actual:
                    self.assertEqual(f2.read(), actual.read())
        finally:
            try:
                os.unlink(f"cases/{case}{ext}")
            except FileNotFoundError:
                pass


if __name__ == "__main__":
    unittest.main()
