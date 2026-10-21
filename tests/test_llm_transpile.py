import argparse
import importlib.util
import sys
from pathlib import Path
from unittest.mock import Mock

import pytest

import py2many
import py2many.cli
from py2many.cli import main


@pytest.fixture
def llm_module(monkeypatch):
    # Stub both platform backends so optional LLM packages are not required.
    backend = Mock()
    monkeypatch.setitem(sys.modules, "llm", backend)
    monkeypatch.setattr(py2many, "macosx_llm", backend, raising=False)
    spec = importlib.util.spec_from_file_location(
        "py2many.llm_transpile",
        Path(py2many.__file__).with_name("llm_transpile.py"),
    )
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, spec.name, module)
    spec.loader.exec_module(module)
    return module


def test_llm_transpile_reports_successful_files(llm_module):
    filenames = [Path("first.py"), Path("failed.py"), Path("last.py")]
    sources = ['print("first")', 'print("failed")', 'print("last")']
    responses = [
        '```rust\nfn main() { println!("first"); }\n```',
        "No code was generated.",
        '```rust\nfn main() { println!("last"); }\n```',
    ]
    model = llm_module.llm.get_model.return_value
    model.prompt.side_effect = [
        Mock(text=Mock(return_value=response)) for response in responses
    ]

    outputs, successful = llm_module.llm_transpile(
        filenames,
        sources,
        Mock(display_name="Rust"),
        argparse.Namespace(llm_model="test-model"),
    )

    assert outputs == [
        'fn main() { println!("first"); }',
        "FAILED",
        'fn main() { println!("last"); }',
    ]
    assert successful == [filenames[0], filenames[2]]


@pytest.mark.parametrize(
    "response,expected_exit_code,expected_output",
    [
        ("```rust\nfn main() {}\n```", 0, "fn main() {}"),
        ("No code was generated.", 1, ""),
    ],
)
def test_llm_cli_output(
    llm_module, monkeypatch, tmp_path, response, expected_exit_code, expected_output
):
    source = tmp_path / "example.py"
    source.write_text('print("hello")\n')
    outdir = tmp_path / "out"
    model = llm_module.llm.get_model.return_value
    model.prompt.return_value.text.return_value = response
    formatter = Mock(return_value=True)
    monkeypatch.setattr(py2many.cli, "_format_one", formatter)

    rv = main(
        args=[
            "--rust",
            "--llm",
            "--llm-model",
            "test-model",
            str(source),
            "--outdir",
            str(outdir),
        ]
    )

    assert rv == expected_exit_code
    assert (outdir / "example.rs").read_text() == expected_output
    if expected_exit_code == 0:
        formatter.assert_called_once()
    else:
        formatter.assert_not_called()
