import os
import os.path
import sys

from distutils import spawn

from py2many.language import LanguageSettings

from .transpiler import CppListComparisonRewriter, CppTranspiler

USER_HOME = os.path.expanduser("~/")


def _conan_include_dirs():
    CONAN_CATCH2 = "catch2/3.0.1/_/_/package/a25d6c83542b56b72fdaa05a85db5d46f5f0f71c"
    CONAN_CPPITERTOOLS = (
        "cppitertools/2.1/_/_/package/5ab84d6acfe1f23c4fae0ab88f26e3a396351ac9"
    )
    return [
        "-I",
        f"{USER_HOME}/.conan/data/{CONAN_CATCH2}/include",
        "-I",
        f"{USER_HOME}/.conan/data/{CONAN_CPPITERTOOLS}/include",
    ]


def settings(args, env=os.environ):
    clang_format_style = env.get("CLANG_FORMAT_STYLE")
    cxx = env.get("CXX")
    default_cxx = ["clang++", "g++-11", "g++"]
    if cxx:
        if not spawn.find_executable(cxx):
            print(f"Warning: CXX({cxx}) not found")
            cxx = None
    if not cxx:
        for exe in default_cxx:
            if spawn.find_executable(exe):
                cxx = exe
                break
        else:
            cxx = default_cxx[0]
    cxx_flags = env.get("CXXFLAGS")
    if cxx_flags:
        cxx_flags = cxx_flags.split()
    else:
        cxx_flags = ["-std=c++17", "-Wall", "-Werror"]
    cxx_flags = _conan_include_dirs() + cxx_flags
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
