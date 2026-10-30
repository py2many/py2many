"""Tests for the match-as-expression dialect (spy-ast new syntax).

Covers transpiling match expressions through the Rust and V backends
(native ``match``) and the CPython backend (desugared to ``IfExp``
chains), using ``tests/match_expr_parser.py`` — a small arithmetic
expression parser written with match expressions, including nested and
parenthesized matches.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from py2many.cli import main

FIXTURE = Path(__file__).parent / "match_expr_parser.py"
RUST_RUNNER = Path(__file__).parent.parent / "scripts" / "rust-runner.sh"

EXPECTED_OUTPUT = "14\n20\n6\n65\n14\n10\n20\n0\n22\n21\n12\n11\n0\n"


def test_example_parses_with_spy_ast():
    import spy_ast

    tree = spy_ast.parse(FIXTURE.read_text())
    assert tree is not None


def test_rust_transpile_match_expression(tmp_path):
    outdir = tmp_path / "rs"
    rv = main(args=["--rust", str(FIXTURE), "--outdir", str(outdir)])
    assert rv == 0
    generated = (outdir / "match_expr_parser.rs").read_text()
    assert "match op {" in generated
    assert "1 => (left + right)" in generated
    assert "_ => 0" in generated
    assert "match code {" in generated
    assert "_ => -1" in generated
    # nested and parenthesized matches map to nested Rust matches
    assert "match match code {" in generated
    assert "match precedence(op1) {" in generated


@pytest.mark.skipif(shutil.which("v") is None, reason="v not available")
def test_vlang_match_runs(tmp_path):
    outdir = tmp_path / "v"
    rv = main(args=["--vlang", str(FIXTURE), "--outdir", str(outdir)])
    assert rv == 0
    generated = outdir / "match_expr_parser.v"
    text = generated.read_text()
    assert "match op {" in text
    assert "match match code {" in text
    proc = subprocess.run(
        ["v", "run", str(generated)],
        capture_output=True,
        text=True,
        cwd=tmp_path,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == EXPECTED_OUTPUT


def test_python_transpile_match_runs(tmp_path):
    outdir = tmp_path / "py"
    rv = main(args=["--python", str(FIXTURE), "--outdir", str(outdir)])
    assert rv == 0
    generated = outdir / "match_expr_parser.py"
    # The new syntax must be desugared: CPython has no match expression.
    assert "match " not in generated.read_text()
    proc = subprocess.run(
        [sys.executable, str(generated)], capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == EXPECTED_OUTPUT


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


@pytest.mark.skipif(shutil.which("cargo") is None, reason="cargo not available")
def test_rust_match_runs(tmp_path):
    outdir = tmp_path / "rs"
    rv = main(args=["--rust", str(FIXTURE), "--outdir", str(outdir)])
    assert rv == 0
    generated = outdir / "match_expr_parser.rs"
    proc = subprocess.run(
        [str(RUST_RUNNER), "compile", str(generated)],
        capture_output=True,
        text=True,
        cwd=tmp_path,
    )
    assert proc.returncode == 0, proc.stderr
    exe = tmp_path / "common-rust-proj" / "target" / "debug" / "match_expr_parser"
    proc = subprocess.run([str(exe)], capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == EXPECTED_OUTPUT
