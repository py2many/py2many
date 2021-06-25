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


def assert_only_init_successful(successful, format_errors=None, failures=None):
    assert {i.name for i in successful} == {"__init__.py"}


def assert_reformat_fails(successful, format_errors, failures):
    assert_only_init_successful(successful, format_errors, failures)
    assert not failures


def assert_no_failures(successful, format_errors, failures, expected_success):
    assert not failures
    assert {i.name for i in successful if i.name != "__init__.py"} == expected_success


class SelfTranspileTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4, extension=False))

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        transpiler_module = ROOT_DIR / "pyrs"
        assert_reformat_fails(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
            )
        )

        assert_no_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=False,
            ),
            expected_success={
                "annotation_transformer.py",
                "context.py",
                "nesting_transformer.py",
                "result.py",
            },
        )

    def test_dart_recursive(self):
        settings = self.SETTINGS["dart"]

        transpiler_module = ROOT_DIR / "pydart"
        assert_only_init_successful(
            *_process_dir(
                settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
            )
        )

        assert_no_failures(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=False,
            ),
            expected_success={
                "annotation_transformer.py",
                "context.py",
                "nesting_transformer.py",
            },
        )

    def test_kotlin_recursive(self):
        settings = self.SETTINGS["kotlin"]

        suppress_exceptions = False
        if not SHOW_ERRORS and settings.formatter:
            if not spawn.find_executable(settings.formatter[0]):
                suppress_exceptions = FileNotFoundError

        transpiler_module = ROOT_DIR / "pykt"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        if not suppress_exceptions:
            assert_only_init_successful(successful)

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        if suppress_exceptions:
            raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        assert_no_failures(
            successful,
            format_errors,
            failures,
            expected_success={
                "annotation_transformer.py",
                "context.py",
                "nesting_transformer.py",
            },
        )

    def test_go_recursive(self):
        settings = self.SETTINGS["go"]
        if SHOW_ERRORS:
            suppress_exceptions = False
        else:
            suppress_exceptions = NotImplementedError

        transpiler_module = ROOT_DIR / "pygo"
        assert_only_init_successful(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            )
        )

        if not SHOW_ERRORS:
            suppress_exceptions = (NotImplementedError, IndexError)

        assert_only_init_successful(
            *_process_dir(
                settings,
                PY2MANY_MODULE,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            )
        )

    def test_nim_recursive(self):
        settings = self.SETTINGS["nim"]
        suppress_exceptions = False
        if not SHOW_ERRORS:
            suppress_exceptions = AttributeError

        transpiler_module = ROOT_DIR / "pynim"
        assert_only_init_successful(
            *_process_dir(
                settings,
                transpiler_module,
                OUT_DIR,
                _suppress_exceptions=suppress_exceptions,
            )
        )

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert set(successful) == {
            PY2MANY_MODULE / "__init__.py",
            PY2MANY_MODULE / "__main__.py",
            PY2MANY_MODULE / "result.py",
        }
        assert len(failures) == 4

    def test_cpp_recursive(self):
        settings = self.SETTINGS["cpp"]
        suppress_exceptions = False
        if not SHOW_ERRORS:
            suppress_exceptions = NotImplementedError

        transpiler_module = ROOT_DIR / "pycpp"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert len(successful) == 10
        assert set(failures) == {
            transpiler_module / "plugins.py",
            transpiler_module / "transpiler.py",
        }

        if not SHOW_ERRORS:
            suppress_exceptions = (
                AttributeError,
                NotImplementedError,
                TypeError,
            )
        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert len(successful) == 9
        assert len(failures) == 6

    def test_julia_recursive(self):
        settings = self.SETTINGS["julia"]

        suppress_exceptions = False
        if not SHOW_ERRORS:
            suppress_exceptions = (NotImplementedError,)
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
            assert set(successful) == {
                transpiler_module / "__init__.py",
                transpiler_module / "plugins.py",
            }

        if not SHOW_ERRORS:
            suppress_exceptions = suppress_exceptions + (ValueError,)

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        if FileNotFoundError in suppress_exceptions:
            raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        assert set(successful) == {
            PY2MANY_MODULE / "__init__.py",
            PY2MANY_MODULE / "__main__.py",
            PY2MANY_MODULE / "annotation_transformer.py",
            PY2MANY_MODULE / "nesting_transformer.py",
            PY2MANY_MODULE / "result.py",
        }
