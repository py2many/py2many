import os
import unittest
from pathlib import Path
from shutil import rmtree
from unittest.mock import Mock

from py2many.cli import _get_all_settings, _process_dir
from py2many.exceptions import (
    AstNotImplementedError,
    AstTypeNotSupported,
    AstUnrecognisedBinOp,
)

SHOW_ERRORS = os.environ.get("SHOW_ERRORS", False)

TESTS_DIR = Path(__file__).parent
ROOT_DIR = TESTS_DIR.parent
OUT_DIR = TESTS_DIR / "output"
PY2MANY_MODULE = ROOT_DIR / "py2many"
dunder_init_dot_py = "__init__.py"


def assert_only_init_successful(successful, format_errors=None, failures=None):
    assert {i.name for i in successful} == {dunder_init_dot_py}


def assert_reformat_fails(successful, format_errors, failures):
    assert_only_init_successful(successful, format_errors, failures)
    assert not failures


def assert_no_failures(successful, format_errors, failures, expected_success):
    assert {
        i.name for i in successful if i.name != dunder_init_dot_py
    } == expected_success
    assert not failures


def assert_some_failures(successful, format_errors, failures, expected_success):
    assert {
        i.name for i in successful if i.name != dunder_init_dot_py
    } == expected_success
    assert failures


def assert_only_reformat_failures(successful, format_errors, failures):
    assert successful
    assert not failures
    assert format_errors


def assert_counts(
    successful, format_errors, failures, format_error_count, failure_count
):
    assert (
        len(format_errors) == format_error_count
    ), f"{len(format_errors)} != {format_error_count}"
    assert len(failures) == failure_count, f"{len(failures)} != {failure_count}"


class SelfTranspileTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4, extension=False))

    def setUp(self):
        rmtree(OUT_DIR, ignore_errors=True)

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        transpiler_module = ROOT_DIR / "pyrs"
        assert_only_reformat_failures(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, False, _suppress_exceptions=False
            )
        )

        expected_file = OUT_DIR / "transpiler.rs"
        assert expected_file.is_file(), f"{expected_file} missing"

        assert_only_reformat_failures(
            *_process_dir(
                settings, PY2MANY_MODULE, OUT_DIR, False, _suppress_exceptions=False
            )
        )

    def test_dart_recursive(self):
        settings = self.SETTINGS["dart"]

        transpiler_module = ROOT_DIR / "pydart"
        assert_only_reformat_failures(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, False, _suppress_exceptions=False
            )
        )

        assert_only_reformat_failures(
            *_process_dir(
                settings, PY2MANY_MODULE, OUT_DIR, False, _suppress_exceptions=False
            )
        )

    def test_dlang_recursive(self):
        settings = self.SETTINGS["dlang"]
        suppress_exceptions = (
            False if SHOW_ERRORS else (AstNotImplementedError, AstUnrecognisedBinOp)
        )

        transpiler_module = ROOT_DIR / "pyd"

        assert_some_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success={"clike.py"},
        )
        assert_counts(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            format_error_count=10,
            failure_count=17,
        )

    def test_kotlin_recursive(self):
        settings = self.SETTINGS["kotlin"]
        suppress_exceptions = False if SHOW_ERRORS else AstTypeNotSupported

        transpiler_module = ROOT_DIR / "pykt"
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            )
        )

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            False,
            _suppress_exceptions=suppress_exceptions,
        )

        assert_only_reformat_failures(successful, format_errors, failures)

    def test_go_recursive(self):
        settings = self.SETTINGS["go"]

        suppress_exceptions = False if SHOW_ERRORS else AstTypeNotSupported

        transpiler_module = ROOT_DIR / "pygo"
        assert_some_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success=set(["transpiler.py"]),
        )

        assert_some_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success={
                "__main__.py",
                "analysis.py",
                "annotation_transformer.py",
                "ast_helpers.py",
                "astx.py",
                "cli.py",
                "context.py",
                "declaration_extractor.py",
                "exceptions.py",
                "helpers.py",
                "language.py",
                "mutability_transformer.py",
                "nesting_transformer.py",
                "process_helpers.py",
                "python_transformer.py",
                "result.py",
                "rewriters.py",
                "scope.py",
                "toposort_modules.py",
                "tracer.py",
            },
        )

    def test_nim_recursive(self):
        settings = self.SETTINGS["nim"]
        suppress_exceptions = False if SHOW_ERRORS else AstTypeNotSupported

        transpiler_module = ROOT_DIR / "pynim"
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            )
        )
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            )
        )

    def test_cpp_recursive(self):
        settings = self.SETTINGS["cpp"]

        transpiler_module = ROOT_DIR / "pycpp"
        successful, format_errors, failures = _process_dir(
            settings, transpiler_module, OUT_DIR, False, _suppress_exceptions=False
        )
        assert len(successful) == 5

        successful, format_errors, failures = _process_dir(
            settings, PY2MANY_MODULE, OUT_DIR, False, _suppress_exceptions=False
        )
        assert len(successful) >= 15

    def test_julia_recursive(self):
        settings = self.SETTINGS["julia"]
        suppress_exceptions = False

        transpiler_module = ROOT_DIR / "pyjl"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            False,
            _suppress_exceptions=suppress_exceptions,
        )
        assert_only_reformat_failures(successful, format_errors, failures)

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            False,
            _suppress_exceptions=suppress_exceptions,
        )

        assert_only_reformat_failures(successful, format_errors, failures)

    def test_vlang_recursive(self):
        settings = self.SETTINGS["vlang"]
        suppress_exceptions = (
            False if SHOW_ERRORS else (AstNotImplementedError, AstUnrecognisedBinOp)
        )

        transpiler_module = ROOT_DIR / "pyv"

        assert_some_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success={"clike.py"},
        )
        assert_counts(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                False,
                _suppress_exceptions=suppress_exceptions,
            ),
            format_error_count=10,
            failure_count=12,
        )
