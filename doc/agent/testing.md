# Testing Guide

## Test Structure

- `tests/cases/` - Python source files for transpilation
- `tests/expected/` - Expected transpiled output by language
- `tests/test_transpiler.py` - Main test suite

## Running Tests Locally

```bash
# All tests
pytest

# Specific language (rust, cpp, go, julia, kotlin, nim, dart, etc.)
pytest tests/test_transpiler.py -k rust

# CLI tests
pytest -k cli -v
```

## Running Tests via GitHub Actions

The project has a **Flexible Matrix** workflow (`.github/workflows/main.yml`) that lets you select a specific language to test:

1. Go to **Actions > Flexible Matrix > Run workflow**
2. Select the language from the dropdown: `cpp`, `dart`, `go`, `julia`, `kotlin`, `nim`, `smt`, `vlang`, `dlang`, `mojo`, `zig`, or leave empty for all
3. Optionally select OS and Python version
4. Click **Run workflow**

This is useful when you only want to test changes for a specific target language.

## Updating Expected Output

When making changes to transpiler behavior:

```bash
export UPDATE_EXPECTED=1
pytest-3 -k cli -v
```

Review changes in `tests/expected/` before committing.

## Debugging Generated Files

```bash
export KEEP_GENERATED=1
pytest-3 -k some_test -v
```

## CI Pipeline

### Option 1: Using act

Run tests locally using act (uses GitHub's heavy Docker images):

```bash
# All tests (push event)
act --reuse

# Specific language via workflow_dispatch
act workflow_dispatch --input focus=vlang

# Run specific job
act --reuse --job build
```

### Option 2: Custom Docker (Recommended for speed)

Build a lighter image using Arch Linux. Pass language flags to install only what you need:

```bash
# Build with specific language
docker build -t py2many/test -f docker/Dockerfile --build-arg VLANG=1 .

# Run tests for that language
docker run --rm -v $(pwd):/src py2many/test pytest -k vlang
```

Available build args (from `docker/Dockerfile`): `RUST`, `CPP`, `GOLANG`, `JULIA`, `NIM`, `KOTLIN`, `DART`, `VLANG`, `SMT`, `DLANG`, `MOJO`, `ZIG`

## Test Checklist

- [ ] All tests pass for target language
- [ ] Transpiled code compiles in target language
- [ ] Expected output updated if behavior changed
- [ ] Lint passes (`ruff check .`)
