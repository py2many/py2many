import os
import os.path
import pathlib
import sys
from itertools import chain

from py2many.language import LanguageSettings
from py2many.process_helpers import find_executable

from .transpiler import CppListComparisonRewriter, CppTranspiler

USER_HOME = os.path.expanduser("~/")
CONAN_ROOTS = [
    f"{USER_HOME}/.conan/",
    f"{USER_HOME}/.conan2/",
]
REQUIRED_INCLUDE_FILES = [
    "catch2/catch_test_macros.hpp",
    "cppitertools/range.hpp",
]


def _conan_include_dirs():
    include_dirs = []
    for hpp_filename in REQUIRED_INCLUDE_FILES:
        for root in CONAN_ROOTS:
            for path in pathlib.Path(root).rglob(hpp_filename):
                include_dirs.append(str(path.parent.parent))
    return include_dirs


def _conan_include_args():
    return list(chain(*(["-I", dir] for dir in _conan_include_dirs())))


def settings(args, env=os.environ):
    clang_format_style = env.get("CLANG_FORMAT_STYLE")
    cxx = env.get("CXX")
    default_cxx = ["clang++", "g++-11", "g++"]
    if cxx:
        if not find_executable(cxx):
            print(f"Warning: CXX({cxx}) not found")
            cxx = None
    if not cxx:
        for exe in default_cxx:
            if find_executable(exe):
                cxx = exe
                break
        else:
            cxx = default_cxx[0]
    cxx_flags = env.get("CXXFLAGS")
    if cxx_flags:
        cxx_flags = cxx_flags.split()
    else:
        cxx_flags = ["-std=c++17", "-Wall", "-Werror"]
    cxx_flags = _conan_include_args() + cxx_flags
    if cxx.startswith("clang++") and not sys.platform == "win32":
        cxx_flags += ["-stdlib=libc++"]

    if clang_format_style:
        clang_format_cmd = ["clang-format", f"-style={clang_format_style}", "-i"]
    else:
        clang_format_cmd = ["clang-format", "-i"]

    return LanguageSettings(
        CppTranspiler(args.extension, args.no_prologue),
        ".cpp",
        "C++",
        clang_format_cmd,
        None,
        [CppListComparisonRewriter()],
        linter=[cxx, *cxx_flags],
    )
