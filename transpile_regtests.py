#!/usr/bin/env python
import os
from os.path import join, dirname, realpath, splitext

from py14.transpiler import transpile


def is_test(filename):
    return filename.startswith("test") and filename.endswith(".py")


def transpile_tests(tests_dir):
    """
    Transpile all python regression tests in tests_dir into C++ header
    files and include them in a single cpp file
    """
    hpp_files = []
    py_files = [p for p in os.listdir(tests_dir) if is_test(p)]

    for py_file in py_files:
        hpp_file = splitext(py_file)[0] + ".hpp"
        hpp_path = join(tests_dir, hpp_file)

        with open(hpp_path, "w") as cpp_file:
            source = open(join(tests_dir, py_file)).read()
            cpp = transpile(source, headers=True, testing=True)
            cpp_file.write(cpp)

        hpp_files.append(hpp_file)

    with open(join(tests_dir, "main.cpp"), "w") as main:
        main.write("#define CATCH_CONFIG_MAIN\n")
        main.write('#include "catch.hpp"\n')
        for hpp_file in hpp_files:
            main.write('#include "{0}"\n'.format(hpp_file))


if __name__ == "__main__":
    tests_dir = join(dirname(realpath(__file__)), "regtests")
    transpile_tests(tests_dir)
