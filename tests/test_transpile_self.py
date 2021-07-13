import os
import unittest

from distutils import spawn
from pathlib import Path
from shutil import rmtree
from unittest.mock import Mock

from py2many.cli import _get_all_settings, _process_dir
from py2many.exceptions import AstTypeNotSupported

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


class SelfTranspileTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4, extension=False))

    def setUp(self):
        rmtree(OUT_DIR, ignore_errors=True)

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        transpiler_module = ROOT_DIR / "pyrs"
        assert_only_reformat_failures(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
            )
        )

        expected_file = OUT_DIR / "tests" / "test_clike.rs"
        assert expected_file.is_file(), f"{expected_file} missing"

        assert_only_reformat_failures(
            *_process_dir(
                settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=False
            ),
        )

    def test_dart_recursive(self):
        settings = self.SETTINGS["dart"]

        transpiler_module = ROOT_DIR / "pydart"
        assert_only_reformat_failures(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
            ),
        )

        assert_only_reformat_failures(
            *_process_dir(
                settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=False
            ),
        )

    def test_kotlin_recursive(self):
        settings = self.SETTINGS["kotlin"]

        suppress_exceptions = False
        if not SHOW_ERRORS and settings.formatter:
            if not spawn.find_executable(settings.formatter[0]):
                suppress_exceptions = FileNotFoundError

        transpiler_module = ROOT_DIR / "pykt"
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            )
        )

        successful, format_errors, failures = _process_dir(
            settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=suppress_exceptions
        )
        if suppress_exceptions:
            raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        assert_only_reformat_failures(
            successful,
            format_errors,
            failures,
        )

    def test_go_recursive(self):
        settings = self.SETTINGS["go"]
        suppress_exceptions = False if SHOW_ERRORS else AstTypeNotSupported

        transpiler_module = ROOT_DIR / "pygo"
        assert_some_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success=set(["transpiler.py"]),
        )

        assert_some_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success={
                "__main__.py",
                "analysis.py",
                "annotation_transformer.py",
                "ast_helpers.py",
                "astx.py",
                "context.py",
                "cli.py",
                "declaration_extractor.py",
                "exceptions.py",
                "language.py",
                "mutability_transformer.py",
                "nesting_transformer.py",
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

        transpiler_module = ROOT_DIR / "pynim"
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=False,
            )
        )
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=False,
            ),
        )

    def test_cpp_recursive(self):
        settings = self.SETTINGS["cpp"]

        transpiler_module = ROOT_DIR / "pycpp"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=False,
        )
        assert len(successful) >= 11

        successful, format_errors, failures = _process_dir(
            settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=False
        )
        assert len(successful) >= 15

    def test_julia_recursive(self):
        settings = self.SETTINGS["julia"]
        suppress_exceptions = (False,)

        if not SHOW_ERRORS:
            if settings.formatter:
                if not spawn.find_executable(settings.formatter[0]):
                    suppress_exceptions = (FileNotFoundError,)

        transpiler_module = ROOT_DIR / "pyjl"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        if FileNotFoundError not in suppress_exceptions:
            assert_only_reformat_failures(successful, format_errors, failures)

        successful, format_errors, failures = _process_dir(
            settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=suppress_exceptions
        )
        if FileNotFoundError in suppress_exceptions:
            raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        assert_only_reformat_failures(
            successful,
            format_errors,
            failures,
        )
