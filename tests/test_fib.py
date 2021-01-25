import os
import sys
import unittest


from pathlib import Path
from py2many import main


class CodeGeneratorTests(unittest.TestCase):
    TEST_CASE = "cases/fib.py"
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
        sys.argv = ["test", "--cpp=1", self.TEST_CASE]
        main()
        with open("expected/fib.cpp") as f2, open("cases/fib.cpp") as actual:
            self.assertEqual(f2.read(), actual.read())

    def test_rust(self):
        sys.argv = ["test", "--rust=1", self.TEST_CASE]
        main()
        with open("expected/fib.rs") as f2, open("cases/fib.rs") as actual:
            self.assertEqual(f2.read(), actual.read())

    def test_julia(self):
        sys.argv = ["test", "--julia=1", self.TEST_CASE]
        main()
        with open("expected/fib.jl") as f2, open("cases/fib.jl") as actual:
            self.assertEqual(f2.read(), actual.read())

    def test_kotlin(self):
        sys.argv = ["test", "--kotlin=1", self.TEST_CASE]
        main()
        with open("expected/fib.kt") as f2, open("cases/fib.kt") as actual:
            self.assertEqual(f2.read(), actual.read())

    def test_nim(self):
        sys.argv = ["test", "--nim=1", self.TEST_CASE]
        main()
        with open("expected/fib.nim") as f2, open("cases/fib.nim") as actual:
            self.assertEqual(f2.read(), actual.read())


if __name__ == "__main__":
    unittest.main()
