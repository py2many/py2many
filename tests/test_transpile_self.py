import os.path
import unittest

from distutils import spawn
from pathlib import Path
from unittest.mock import Mock

from py2many.cli import _get_all_settings, _process_dir

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

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        transpiler_module = ROOT_DIR / "pyrs"
        assert_only_reformat_failures(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
            )
        )

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
        suppress_exceptions = False if SHOW_ERRORS else NotImplementedError

        transpiler_module = ROOT_DIR / "pygo"
        assert_some_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success=set(),
        )

        assert_some_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            ),
            expected_success={"result.py", "__main__.py", "astx.py"},
        )

    def test_nim_recursive(self):
        settings = self.SETTINGS["nim"]
        suppress_exceptions = False if SHOW_ERRORS else NotImplementedError

        transpiler_module = ROOT_DIR / "pynim"
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            )
        )
        assert_only_reformat_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            ),
        )

    def test_cpp_recursive(self):
        settings = self.SETTINGS["cpp"]
        suppress_exceptions = False if SHOW_ERRORS else NotImplementedError

        transpiler_module = ROOT_DIR / "pycpp"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert len(successful) >= 11

        successful, format_errors, failures = _process_dir(
            settings, PY2MANY_MODULE, OUT_DIR, _suppress_exceptions=suppress_exceptions
        )
        assert len(successful) >= 15

    def test_julia_recursive(self):
        settings = self.SETTINGS["julia"]
        suppress_exceptions = (False,) if SHOW_ERRORS else (NotImplementedError,)

        if not SHOW_ERRORS:
            if settings.formatter:
                if not spawn.find_executable(settings.formatter[0]):
                    suppress_exceptions = (FileNotFoundError, NotImplementedError)

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
