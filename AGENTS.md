# AGENTS.md - Agent Guidelines for py2many

## Project Overview
py2many transpiles Python code to Rust, C++, Go, Zig, Julia, Nim, Dart, V, D, and Kotlin.

## Development Commands
```bash
# Run tests
pytest

# Run specific language tests
pytest tests/test_transpiler.py -k rust

# Lint
ruff check .

# Type check
pyright .
```

## Code Style
- Follow PEP 8 with 120 character line limit
- Use type hints for all public functions
- Run `ruff check . --fix` before committing

## Adding New Language Support
1. Create a transpiler class in `py2many/transpilers/`
2. Add language flag to CLI in `py2many/__main__.py`
3. Add test cases in `tests/cases/` and expected output in `tests/expected/`
4. Update README.md with supported languages

## Key Files
- `py2many/transpilers/` - Language transpiler implementations
- `tests/` - Test cases and expected outputs
- `doc/langspec.md` - Language specification notes

## Important Notes
- Use explicit returns (don't rely on Python's implicit return)
- Handle Python-specific features carefully (list comprehensions, decorators)
- Test all transpiled code compiles in target language
