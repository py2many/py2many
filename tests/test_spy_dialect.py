"""Tests for the spy-dialect path: cases that are not valid
CPython but parse with spy-ast (e.g. match expressions).

Full programs using match expressions live in ``tests/spy-cases/`` and are
exercised through the shared ``test_cli.py`` matrix (which runs their
``tests/expected/{case}.py`` python backend output for golden output). The tests here cover
what the matrix cannot: single-evaluation of hoisted subjects and the
missing-wildcard error.
"""

import ast
import subprocess
import sys
from pathlib import Path

import pytest
import spy_ast

from py2many.cli import main

TESTS_DIR = Path(__file__).parent


def test_python_match_subject_evaluated_once(tmp_path):
    source = tmp_path / "once.py"
    source.write_text(
        "def f(x: int) -> int:\n"
        "    print(1)\n"
        "    return x\n"
        "def describe(x: int) -> int:\n"
        "    return match f(x):\n"
        "        1: 10\n"
        "        _: 20\n"
        'if __name__ == "__main__":\n'
        "    print(describe(2))\n"
    )
    outdir = tmp_path / "py"
    rv = main(args=["--python", str(source), "--outdir", str(outdir)])
    assert rv == 0
    proc = subprocess.run(
        [sys.executable, str(outdir / "once.py")],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    # f(x) evaluated exactly once despite appearing in every test
    assert proc.stdout == "1\n20\n"


def test_python_match_missing_wildcard_fails(tmp_path):
    source = tmp_path / "nowrap.py"
    source.write_text(
        "def describe(x: int) -> int:\n"
        "    return match x:\n"
        "        1: 10\n"
        'if __name__ == "__main__":\n'
        "    print(describe(1))\n"
    )
    outdir = tmp_path / "py"
    rv = main(args=["--python", str(source), "--outdir", str(outdir)])
    assert rv != 0


@pytest.mark.parametrize(
    "case", sorted((TESTS_DIR / "cases").glob("*.py")), ids=lambda p: p.stem
)
def test_cases_are_cpython(case):
    # Dialect sources belong in tests/spy-cases, not tests/cases.
    ast.parse(case.read_text(), filename=str(case))


@pytest.mark.parametrize(
    "case", sorted((TESTS_DIR / "spy-cases").glob("*.py")), ids=lambda p: p.stem
)
def test_spy_cases_are_dialect(case):
    source = case.read_text()
    # Valid CPython belongs in tests/cases, not tests/spy-cases.
    with pytest.raises(SyntaxError):
        ast.parse(source, filename=str(case))
    spy_ast.parse(source)
