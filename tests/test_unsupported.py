import ast
import os.path
import unittest
import sys
from distutils import spawn
from pathlib import Path
from subprocess import run
from textwrap import dedent
from unittest.mock import Mock

import astpretty

from unittest_expander import foreach, expand

from py2many.cli import transpile, _get_all_settings

TESTS_DIR = Path(__file__).parent
ROOT_DIR = TESTS_DIR.parent

KEEP_GENERATED = os.environ.get("KEEP_GENERATED", False)
UPDATE_EXPECTED = os.environ.get("UPDATE_EXPECTED", False)
CXX = os.environ.get("CXX", "clang++")
ENV = {"rust": {"RUSTFLAGS": "--deny warnings"}}
COMPILERS = {
    "cpp": [CXX, "-std=c++14", "-I", str(ROOT_DIR), "-stdlib=libc++"],
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

_INT_ENUM = dedent(
    """
    from enum import IntEnum, auto
    class Colors(IntEnum):
        RED = auto()
        GREEN = auto()
        BLUE = auto()
"""
)
_INT_FLAG = dedent(
    """
    from enum import IntFlag
    class Permissions(IntFlag):
        R = 1
        W = 2
        X = 16
    a = Permissions.R | Permissions.W
"""
)

TEST_CASES = {
    "assert_0": "assert not 0",
    "assert_None": "assert not None",
    "dict_value_type": "a = {1: 1, 2: 2.0}",  # https://github.com/adsharma/py2many/issues/171
    "empty_print": "print()",
    "fstring": "assert f'{1+1}'",  # https://github.com/adsharma/py2many/issues/74
    "str_format": "ab = '{}{}'.format('a', 'b')",  # https://github.com/adsharma/py2many/issues/73
    "percent_formatting": "a = '~ %s ~' % 'a'",  # https://github.com/adsharma/py2many/issues/176
    "tuple_destruct": "foo, (baz, qux) = 4, (5, 6); assert foo != (baz != qux)",  # https://github.com/adsharma/py2many/issues/155
    "float_1": "a = float(1)",  # https://github.com/adsharma/py2many/issues/129
    "print_None": "print(None)",
    "class_vars": "class A:\n  B = 'FOO'\ndef main(): assert A.B == 'FOO'",  # https://github.com/adsharma/py2many/issues/144
    "default_init": dedent(
        """
        class Rectangle:
            def __init__(self, height=0, length=0):
                self.height = height
                self.length = length

        def main(): r = Rectangle()
    """
    ),  # https://github.com/adsharma/py2many/issues/143
    "complex_dict": "a = ('a', ); b = {a: 'a'}; assert 'a' == b[a]",
    "simple_dict": "l_b = {'a': 0}; assert 'a' in l_b",
    "annassign_List": "from typing import List; items : List = ['a', 'b']; print(items)",
    "intenum_iter": f"{_INT_ENUM}\ndef main():\n  for val in Colors:    print(val)",  # https://github.com/adsharma/py2many/issues/31
    "intflag_bitop": f"{_INT_FLAG}\ndef main():\n  if a & Permissions.R:    print('R')",  # https://github.com/adsharma/py2many/issues/115
    "bool_to_int": "print(int(True))",  # https://github.com/adsharma/py2many/issues/130
    "bool_plus_int": "print(True+1)",  # https://github.com/adsharma/py2many/issues/131
    "del": "a = 1; del a",
    "dict_empty": "assert not {}",
    "dict_del": "a = {1: 1}; del a[1]; assert not a",
    "dict_order": "a = {1: 1, 2: 2, 3: 3}; del a[2]; a[2] = 2; assert list(a.keys()) == [1, 3, 2]",
}

# NOTE: Inclusion here does not indicate that the case is comparable
EXPECTED_SUCCESSES = [
    "annassign_List.dart",
    "assert_None.dart",
    "bool_plus_int.jl",
    "bool_plus_int.rs",
    "bool_to_int.jl",
    "bool_to_int.nim",
    "bool_to_int.rs",
    "complex_dict.jl",
    "complex_dict.nim",
    "del.rs",
    "dict_value_type.dart",
    "dict_value_type.jl",
    "dict_value_type.kt",
    "empty_print.dart",
    "empty_print.jl",
    "empty_print.kt",
    "empty_print.rs",
    "intenum_iter.nim",
    "float_1.jl",
    "float_1.nim",
    "print_None.dart",
    "print_None.jl",
    "simple_dict.kt",
    "simple_dict.nim",
    "str_format.go",
    "str_format.kt",
    "tuple_destruct.jl",
]


def has_main(source):
    lines = source.splitlines()
    return bool(
        [line in line for line in lines if "def main" in line or "__main__" in line]
    )


@expand
class CodeGeneratorTests(unittest.TestCase):
    LANGS = list(_get_all_settings(Mock(indent=4)).keys())
    maxDiff = None

    def setUp(self):
        os.chdir(TESTS_DIR)

    @foreach(sorted(LANGS))
    @foreach(sorted(TEST_CASES.keys()))
    def test_snippet(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        ext = settings.ext
        source_data = TEST_CASES[case]
        is_script = has_main(source_data)
        if ext in [".dart", ".kt", ".rs"] and not is_script:
            source_data = f"def main():\n  {source_data}"
        print(f">{source_data}<")
        tree = ast.parse(source_data)
        astpretty.pprint(tree)
        proc = run([sys.executable, "-c", source_data], capture_output=True)
        if proc.returncode:
            raise RuntimeError(f"Invalid case {case}:\n{proc.stdout}{proc.stderr}")
        try:
            result = transpile(
                tree,
                settings.transpiler,
                settings.rewriters,
                settings.transformers,
                settings.post_rewriters,
            )
        except NotImplementedError as e:
            raise unittest.SkipTest(str(e))

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

        case_output = TESTS_DIR / "cases" / f"{case}{ext}"
        expect_success = f"{case}{ext}" in EXPECTED_SUCCESSES

        with open(case_output, "w") as f:
            f.write(result)

        if settings.formatter:
            if settings.ext == ".kt" and case_output.is_absolute():
                # KtLint does not support absolute path in globs
                case_output = case_output.relative_to(Path.cwd())
            proc = run([*settings.formatter, case_output], env=env, capture_output=True)
            if proc.returncode:
                raise unittest.SkipTest(
                    f"Error: Could not reformat using {settings.formatter}:\n{proc.stdout}{proc.stderr}"
                )

        try:
            compiler = COMPILERS[lang]
            if compiler:
                if not spawn.find_executable(compiler[0]):
                    raise unittest.SkipTest(f"{compiler[0]} not available")
                proc = run([*compiler, case_output], env=env, capture_output=True)

                if proc.returncode and not expect_success:
                    raise unittest.SkipTest(
                        f"{case}{ext} doesnt compile:\n{proc.stdout}{proc.stderr}"
                    )

            if exe.exists() and os.access(exe, os.X_OK):
                if not expect_success:
                    raise AssertionError(f"{case}{ext} compiled")

            elif INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if not spawn.find_executable(invoker[0]):
                    raise unittest.SkipTest(f"{invoker[0]} not available")
                proc = run([*invoker, case_output], env=env, capture_output=True)

                if proc.returncode and not expect_success:
                    raise unittest.SkipTest(
                        f"Execution of {case}{ext} failed:\n{proc.stdout}{proc.stderr}"
                    )
                if not expect_success:
                    raise AssertionError(f"{case}{ext} invoked")
            else:
                return

        finally:
            if not KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
            exe.unlink(missing_ok=True)

        if not expect_success:
            assert False


if __name__ == "__main__":
    unittest.main()
