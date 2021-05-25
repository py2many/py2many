import os.path
import unittest
from pathlib import Path
from unittest.mock import Mock

from py2many.cli import _get_all_settings, _process_dir

SHOW_ERRORS = os.environ.get("SHOW_ERRORS", False)

TESTS_DIR = Path(__file__).parent
ROOT_DIR = TESTS_DIR.parent
OUT_DIR = TESTS_DIR / "output"


class SelfTranspileTests(unittest.TestCase):
    SETTINGS = _get_all_settings(Mock(indent=4))

    def test_rust_recursive(self):
        settings = self.SETTINGS["rust"]

        pyrs_module = ROOT_DIR / "pyrs"
        successful, format_errors, failures = _process_dir(
            settings, pyrs_module, OUT_DIR, _suppress_exceptions=False
        )
        assert len(successful) == 2  # The two __init__.py

        pyrs_module = ROOT_DIR / "py2many"
        successful, format_errors, failures = _process_dir(
            settings,
            pyrs_module,
            OUT_DIR,
            _suppress_exceptions=(NotImplementedError,),
        )
        assert len(successful) == 4  # Four files transpile ok
