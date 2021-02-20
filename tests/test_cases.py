import os
import sys
import unittest


from pathlib import Path
from py2many import main


class CodeGeneratorTests(unittest.TestCase):
    TEST_CASES = ["fib", "rect", "infer", "infer-ops", "binit", "lambda", "int_enum"]
    TESTS_DIR = Path(__file__).parent

    def setUp(self):
        os.chdir(self.TESTS_DIR)

    def tearDownClass():
        return
        os.unlink("cases/fib.cpp")
        os.unlink("cases/fib.rs")
        os.unlink("cases/fib.jl")
        os.unlink("cases/fib.kt")
        os.unlink("cases/fib.nim")

    def test_cpp(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--cpp=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.cpp") as f2, open(
                f"cases/{case}.cpp"
            ) as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_rust(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--rust=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.rs") as f2, open(f"cases/{case}.rs") as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_julia(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--julia=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.jl") as f2, open(f"cases/{case}.jl") as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_kotlin(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--kotlin=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.kt") as f2, open(f"cases/{case}.kt") as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_nim(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--nim=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.nim") as f2, open(
                f"cases/{case}.nim"
            ) as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_dart(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--dart=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.dart") as f2, open(
                f"cases/{case}.dart"
            ) as actual:
                self.assertEqual(f2.read(), actual.read())

    def test_go(self):
        for case in self.TEST_CASES:
            sys.argv = ["test", "--go=1", f"cases/{case}.py"]
            main()
            with open(f"expected/{case}.go") as f2, open(f"cases/{case}.go") as actual:
                self.assertEqual(f2.read(), actual.read())


if __name__ == "__main__":
    unittest.main()
