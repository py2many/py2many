from pathlib import Path

try:
    from py2many.pycpp import (
        REQUIRED_INCLUDE_FILES,
        _conan_include_args,
        _conan_include_dirs,
    )
except ImportError:
    from pycpp import REQUIRED_INCLUDE_FILES, _conan_include_args, _conan_include_dirs


class TestSettings:
    def test_conan_include_dirs(self):
        include_dirs = _conan_include_dirs()

        assert len(include_dirs) == len(REQUIRED_INCLUDE_FILES)
        for i, path in enumerate(include_dirs):
            assert Path(path, REQUIRED_INCLUDE_FILES[i]).exists()

    def test_conan_include_args(self):
        assert len(_conan_include_args()) == len(REQUIRED_INCLUDE_FILES) * 2
