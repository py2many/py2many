import unittest
from pathlib import Path
from unittest.mock import Mock

from py2many.cli import _get_all_settings

try:
    from py2many.pycpp import (
        REQUIRED_INCLUDE_FILES,
        _conan_include_args,
        _conan_include_dirs,
    )
except ImportError:
    from pycpp import REQUIRED_INCLUDE_FILES, _conan_include_args, _conan_include_dirs


class TestSettings(unittest.TestCase):
    def test_conan_include_dirs(self):
        include_dirs = _conan_include_dirs()

        assert len(include_dirs) == len(REQUIRED_INCLUDE_FILES)
        for i, path in enumerate(include_dirs):
            assert Path(path, REQUIRED_INCLUDE_FILES[i]).exists()

    def test_conan_include_args(self):
        assert len(_conan_include_args()) == len(REQUIRED_INCLUDE_FILES) * 2

    def test_env_clang_format_style(self):
        lang = "cpp"
        env = {"CLANG_FORMAT_STYLE": "Google"}
        settings = _get_all_settings(Mock(indent=4), env=env)[lang]
        self.assertIn("-style=Google", settings.formatter)

    def test_arg_nim_indent(self):
        lang = "nim"
        settings = _get_all_settings(Mock(indent=2))[lang]
        self.assertIn("--indent:2", settings.formatter)
