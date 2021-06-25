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


class SelfTranspileTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4, extension=False))

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        transpiler_module = ROOT_DIR / "pyrs"
        successful, format_errors, failures = _process_dir(
            settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
        )
        assert set([i.name for i in successful]) == {"__init__.py"}

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=False,
        )
        assert set(successful) == {
            PY2MANY_MODULE / "__init__.py",
            PY2MANY_MODULE / "annotation_transformer.py",
            PY2MANY_MODULE / "context.py",
            PY2MANY_MODULE / "exceptions.py",
            PY2MANY_MODULE / "nesting_transformer.py",
            PY2MANY_MODULE / "result.py",
        }

    def test_dart_recursive(self):
        settings = self.SETTINGS["dart"]

        transpiler_module = ROOT_DIR / "pydart"
        successful, format_errors, failures = _process_dir(
            settings, transpiler_module, OUT_DIR, _suppress_exceptions=False
        )
        assert set([i.name for i in successful]) == {"__init__.py"}

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=False,
        )
        assert set(successful) == {
            PY2MANY_MODULE / "__init__.py",
            PY2MANY_MODULE / "annotation_transformer.py",
            PY2MANY_MODULE / "context.py",
            PY2MANY_MODULE / "exceptions.py",
            PY2MANY_MODULE / "nesting_transformer.py",
        }

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
            assert set([i.name for i in successful]) == {"__init__.py"}

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        if suppress_exceptions:
            raise unittest.SkipTest(f"{settings.formatter[0]} not available")

        assert set(successful) == {
            PY2MANY_MODULE / "__init__.py",
            PY2MANY_MODULE / "annotation_transformer.py",
            PY2MANY_MODULE / "context.py",
            PY2MANY_MODULE / "nesting_transformer.py",
        }

    def test_go_recursive(self):
        settings = self.SETTINGS["go"]
        suppress_exceptions = False if SHOW_ERRORS else NotImplementedError

        transpiler_module = ROOT_DIR / "pygo"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert set([i.name for i in successful]) == {"__init__.py"}

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert set([i.name for i in successful]) == {"__init__.py"}

    def test_nim_recursive(self):
        settings = self.SETTINGS["nim"]
        suppress_exceptions = False if SHOW_ERRORS else NotImplementedError

        transpiler_module = ROOT_DIR / "pynim"
        successful, format_errors, failures = _process_dir(
            settings,
            transpiler_module,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert set([i.name for i in successful]) == {"__init__.py"}

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
        assert len(successful) == 10
        assert set(failures) == {
            transpiler_module / "plugins.py",
            transpiler_module / "transpiler.py",
        }

        successful, format_errors, failures = _process_dir(
            settings,
            PY2MANY_MODULE,
            OUT_DIR,
            _suppress_exceptions=suppress_exceptions,
        )
        assert len(successful) == 10
        assert len(failures) == 6

    def test_julia_recursive(self):
        settings = self.SETTINGS["julia"]
        suppress_exceptions = False if SHOW_ERRORS else (NotImplementedError,)

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
            assert set(successful) == {
                transpiler_module / "__init__.py",
                transpiler_module / "plugins.py",
            }

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
