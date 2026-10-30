"""Tests for the spy-dialect path: cases that are not valid
CPython but parse with spy-ast (e.g. match expressions).

Full programs using match expressions live in ``tests/cases/`` and are
exercised through the shared ``test_cli.py`` matrix (which sources golden
output via the python backend for dialect cases). The tests here cover
what the matrix cannot: single-evaluation of hoisted subjects and the
missing-wildcard error.
"""

import subprocess
import sys
from pathlib import Path

from py2many.cli import main


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


def test_dialect_case_detected():
    from tests.test_cli import is_spy_dialect_case

    case_source = Path(__file__).parent / "cases" / "match_expr.py"
    assert is_spy_dialect_case(case_source.read_text())
    assert not is_spy_dialect_case("x = 1\nprint(x)\n")
    # Broken under both parsers: not a dialect case, fails as before.
    assert not is_spy_dialect_case("def broken(:\n")
