#!/usr/bin/env python
import os
import contextlib
from os.path import join, dirname, realpath
from subprocess import check_call
from py14.transpiler import transpile


@contextlib.contextmanager
def temp_chdir(path):
    """
    Usage:
    >>> with temp_chdir(gitrepo_path):
    ... subprocess.call('git status')
    """
    starting_directory = os.getcwd()
    try:
        os.chdir(path)
        yield
    finally:
        os.chdir(starting_directory)


def try_clang_format(filename):
    try:
        check_call(["clang-format", "-i", "-style=LLVM", filename])
    except OSError:
        pass


def try_compile(filename):
    try:
        out_name = os.path.splitext(filename)[0]
        check_call(["clang++", "-Wall", "-std=c++14", "-I../py14/runtime",
                    "-o", out_name, filename])
    except OSError:
        pass


def run_tests(tests_dir):
    for test_path in os.listdir(tests_dir):
        if (test_path.startswith("test") and not
            test_path.endswith(".cpp") and not
            test_path.endswith(".py")):
            with temp_chdir(tests_dir):
                check_call(["./" + test_path], shell=True)


def compile_regression_tests(tests_dir):
    for test_path in os.listdir(tests_dir):
        if test_path.startswith("test") and test_path.endswith(".cpp"):
            with temp_chdir(tests_dir):
                try_compile(test_path)


def generate_cpp_regression_tests(tests_dir):
    for test_path in os.listdir(tests_dir):
        if test_path.startswith("test") and test_path.endswith(".py"):
            source = open(join(tests_dir, test_path)).read()
            cpp = transpile(source, headers=True, testing=True)

            cpp_path = join(tests_dir, os.path.splitext(test_path)[0] + ".cpp")
            with open(cpp_path, "w") as cpp_file:
                cpp_file.write(cpp)
            try_clang_format(cpp_path)


if __name__ == "__main__":
    tests_dir = join(dirname(realpath(__file__)), "regtests")
    generate_cpp_regression_tests(tests_dir)
    compile_regression_tests(tests_dir)
    run_tests(tests_dir)
