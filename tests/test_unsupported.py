import ast
import os.path
import sys
from functools import lru_cache, partial
from itertools import product
from subprocess import run
from textwrap import dedent
from unittest.mock import Mock

import pytest

try:
    from astpretty import pprint as ast_pretty_print
except ImportError:
    if sys.version_info >= (3, 9):
        from ast import dump as ast_dump_raw

        ast_dump = partial(ast_dump_raw, indent=4)
    else:
        from ast import dump as ast_dump

    def ast_pretty_print(node):
        print(ast_dump(node))


from test_cli import BUILD_DIR, COMPILERS, ENV, GENERATED_DIR, INVOKER, KEEP_GENERATED
from test_cli import LANGS as _LANGS
from test_cli import SHOW_ERRORS, TESTS_DIR, get_exe_filename, has_main_lines

import py2many.cli
from py2many.cli import (
    _create_cmd,
    _get_all_settings,
    _relative_to_cwd,
    _transpile,
    _transpile_one,
)
from py2many.exceptions import AstIncompatibleAssign
from py2many.process_helpers import find_executable

LANGS = set(_LANGS) - {"python", "smt"}

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
    "assert_str": "assert 'a'",
    "dict_value_type": "a = {1: 1, 2: 2.0}",  # https://github.com/adsharma/py2many/issues/171
    "empty_print": "print()",
    "list_compre": "[i for i in ['a']]",
    "list_destruct": "[a, b] = [1, 2]",
    "list_slice": "a = [1, 2]; b = a[0:1]",
    "str_compre": "[i for i in 'a']",
    "all": "assert all(i for i in [True])",
    "any": "assert any(i for i in [True])",
    "fstring": "assert f'{1+1}'",  # https://github.com/adsharma/py2many/issues/74
    "str_format": "ab = '{}{}'.format('a', 'b')",  # https://github.com/adsharma/py2many/issues/73
    "percent_formatting": "a = '~ %s ~' % 'a'",  # https://github.com/adsharma/py2many/issues/176
    "str_mult": "'a' * 4",
    "nested_class": dedent(
        """
        class Foo:
            class Inner:
                def f1(self):
                    return self.f2()
                def f2(self) -> int:
                    return 20
        def main(): Foo.Inner().f1()
    """
    ),
    "nested_func": dedent(
        """
        def foo():
            def bar():
                return 1
            return bar()
        def main(): foo()
    """
    ),
    "tuple_destruct": "foo, (baz, qux) = 4, (5, 6); assert foo != (baz != qux)",  # https://github.com/adsharma/py2many/issues/155
    "float_str": "float('2.71')",
    "int_str": "int('7')",
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
    "dict_keys_explicit": "{1: 1}.keys()",  # https://github.com/adsharma/py2many/issues/248
    "dict_keys_compare": "a = {1: 1}; 1 in a.keys()",  # https://github.com/adsharma/py2many/issues/248
    "dict_values": "1 in {1: 1}.values()",
    "dict_get": "assert {1: 2}.get(1) == 2",
    "dict_get_default": "assert {1: 2}.get(3, 3) == 3",
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
TEST_PARAMS = [(case, lang) for case, lang in product(TEST_CASES, LANGS)]

# NOTE: Inclusion here does not indicate that the case is comparable
EXPECTED_SUCCESSES = [
    "all.v",
    "all.jl",
    "annassign_List.dart",
    "annassign_List.v",
    "any.v",
    "any.jl",
    "assert_0.d",
    "assert_None.d",
    "assert_str.d",
    "bool_plus_int.d",
    "bool_plus_int.jl",
    "bool_plus_int.rs",
    "bool_plus_int.v",
    "bool_to_int.d",
    "bool_to_int.jl",
    "bool_to_int.nim",
    "bool_to_int.rs",
    "bool_to_int.v",
    "complex_dict.jl",
    "complex_dict.kt",
    "complex_dict.nim",
    "complex_dict.rs",
    "class_vars.rs",
    "del.d",
    # "del.rs", not sure why this is now broken
    "default_init.dart",
    "dict_empty.d",
    "dict_get.kt",
    "dict_get_default.d",
    "dict_get_default.jl",
    "dict_keys.dart",
    "dict_keys.jl",
    "dict_keys.rs",
    "dict_keys_compare.d",
    "dict_keys_compare.dart",
    "dict_keys_compare.jl",
    "dict_keys_compare.rs",
    "dict_keys_compare.v",
    "dict_keys_explicit.d",
    "dict_keys_explicit.jl",
    "dict_keys_explicit.rs",
    #    "dict_keys_explicit.v", # -translated switch breaks this now, will fix later.
    "dict_value_type.d",
    "dict_value_type.dart",
    "dict_value_type.jl",
    "dict_value_type.kt",
    "dict_values.d",
    "dict_values.jl",
    "dict_values.rs",
    "dict_values.v",
    "empty_print.d",
    "empty_print.dart",
    "empty_print.jl",
    "empty_print.kt",
    "empty_print.rs",
    "intenum_iter.nim",
    "float_1.jl",
    "float_1.nim",
    "float_str.kt",
    "int_str.kt",
    "list_slice.nim",
    "list_slice.v",
    "list_slice.jl",
    "list_destruct.v",
    "nested_class.kt",
    "nested_func.d",
    "nested_func.dart",
    "nested_func.kt",
    "nested_func.rs",
    "print_None.d",
    "print_None.dart",
    "print_None.jl",
    "simple_dict.d",
    "simple_dict.dart",
    "simple_dict.jl",
    "simple_dict.kt",
    "simple_dict.nim",
    "simple_dict.rs",
    "simple_dict.v",
    "str_format.kt",
    "str_mult.dart",
    "str_mult.v",
    "tuple_destruct.jl",
    "str_compre.d",
    "str_compre.jl",
    "list_compre.d",
    "list_compre.jl",
]

TEST_ERROR_CASES = {
    "a: i8 = 300": AstIncompatibleAssign,
    "a: i8 = 10; b: i16 = 300; c: i16 = a + b": AstIncompatibleAssign,
}


def has_main(source):
    lines = source.splitlines()
    return has_main_lines(lines)


@lru_cache()
def get_tree(source_data, ext):
    is_script = has_main(source_data)
    if ext in [".dart", ".kt", ".rs", ".d"] and not is_script:
        source_data = f"if __name__ == '__main__':\n  {source_data}"
    print(f">{source_data}<")
    tree = ast.parse(source_data)
    ast_pretty_print(tree)
    proc = run([sys.executable, "-c", source_data], capture_output=True)
    if proc.returncode:
        raise RuntimeError(f"Invalid case {source_data}:\n{proc.stdout}{proc.stderr}")
    return tree


class TestCodeGenerator:
    maxDiff = None

    SHOW_ERRORS = SHOW_ERRORS

    @classmethod
    def setup_class(cls):
        os.makedirs(BUILD_DIR, exist_ok=True)
        os.chdir(BUILD_DIR)
        py2many.cli.CWD = BUILD_DIR

    @pytest.mark.parametrize("case,lang", TEST_PARAMS)
    def test_snippet(self, case, lang):
        env = os.environ.copy()
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(
            Mock(indent=4, extension=False, no_prologue=False), env=env
        )[lang]
        ext = settings.ext
        tree = get_tree(TEST_CASES[case], ext)

        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        case_output = GENERATED_DIR / f"{case}{ext}"
        try:
            result = _transpile([case_filename], [tree], settings)[0][0]
        except NotImplementedError as e:
            raise pytest.skip(str(e))

        if settings.formatter:
            if not find_executable(settings.formatter[0]):
                raise pytest.skip(f"{settings.formatter[0]} not available")

        exe = get_exe_filename(case, ext)
        exe.unlink(missing_ok=True)

        expect_success = f"{case}{ext}" in EXPECTED_SUCCESSES

        with open(case_output, "w") as f:
            f.write(result)

        if settings.formatter:
            if settings.ext == ".kt" and case_output.is_absolute():
                # KtLint does not support absolute path in globs
                case_output = _relative_to_cwd(case_output)
            proc = run([*settings.formatter, case_output], env=env, capture_output=True)
            if proc.returncode and not self.SHOW_ERRORS:
                raise pytest.skip(
                    f"Error: Could not reformat using {settings.formatter}:\n{proc.stdout}{proc.stderr}"
                )
            assert not proc.returncode

        try:
            compiler = COMPILERS.get(lang)
            if compiler:
                if not find_executable(compiler[0]):
                    raise pytest.skip(f"{compiler[0]} not available")
                cmd = _create_cmd(compiler, filename=case_output, exe=exe)
                proc = run(cmd, env=env, capture_output=True)

                if proc.returncode and not expect_success and not self.SHOW_ERRORS:
                    raise pytest.skip(
                        f"{case}{ext} doesnt compile:\n{proc.stdout}{proc.stderr}"
                    )
                assert not proc.returncode

            if INVOKER.get(lang):
                invoker = INVOKER.get(lang)
                if not find_executable(invoker[0]):
                    raise pytest.skip(f"{invoker[0]} not available")
                proc = run([*invoker, case_output], env=env, capture_output=True)

                if proc.returncode and not expect_success and not self.SHOW_ERRORS:
                    raise pytest.skip(
                        f"Execution of {case}{ext} failed:\n{proc.stdout}{proc.stderr}"
                    )
                if not expect_success:
                    assert (
                        proc.returncode
                    ), f"{case}{ext} invoked successfully:\n{result}"
                if expect_success:
                    assert not proc.returncode, f"{case}{ext} failed"
            elif exe.exists() and os.access(exe, os.X_OK):
                proc = run([exe], env=env, capture_output=True)
                if proc.returncode and not expect_success and not self.SHOW_ERRORS:
                    raise pytest.skip(
                        f"Invocation error {proc.returncode}:\n{proc.stdout}{proc.stderr}"
                    )
                if not expect_success:
                    assert (
                        proc.returncode
                    ), f"{case}{ext} invoked successfully:\n{result}"
                if expect_success:
                    assert not proc.returncode, f"{case}{ext} failed"
            else:
                return

        finally:
            if not KEEP_GENERATED:
                case_output.unlink(missing_ok=True)
                exe.unlink(missing_ok=True)

        if not expect_success:
            assert False

    @pytest.mark.parametrize("lang", LANGS)
    def test_comment_unimplemented_body(self, lang):
        env = os.environ.copy()
        settings = _get_all_settings(
            Mock(indent=4, extension=False, no_prologue=False), env=env
        )[lang]

        case = "unsupported_body"
        case_filename = TESTS_DIR / "cases" / f"{case}.py"
        source_data = dedent(
            """
            def outer():
                a = 1
                def inner():
                    nonlocal a
                    return a
                return inner()


            if __name__ == "__main__":
                x = outer()
                print(x)
        """
        )
        tree = get_tree(source_data, settings.ext)

        settings.transpiler._throw_on_unimplemented = False
        try:
            result = _transpile([case_filename], [tree], settings)[0][0]
            print(result)
            assert "nonlocal unimplemented on line 5:8" in result

        except Exception:
            settings.transpiler._throw_on_unimplemented = True
            raise

    # These tests are expected to fail for all languages
    @pytest.mark.parametrize("case", sorted(TEST_ERROR_CASES))
    def test_error_cases(self, case):
        env = os.environ.copy()
        lang = "rust"  # Just so we avoid running tests N times
        if ENV.get(lang):
            env.update(ENV.get(lang))

        settings = _get_all_settings(Mock(indent=4, extension=False), env=env)[lang]
        ext = settings.ext

        expected_error = TEST_ERROR_CASES[case]
        source_data = "from ctypes import c_int8 as i8, c_int16 as i16\n" + case
        tree = get_tree(source_data, ext)

        try:
            _transpile_one(
                [tree],
                tree,
                settings.transpiler,
                settings.rewriters,
                settings.transformers,
                settings.post_rewriters,
                None,
            )
        except Exception as e:
            assert type(e) == expected_error


if __name__ == "__main__":
    pytest.main()
