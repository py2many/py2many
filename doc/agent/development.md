# Development Guide

## Setting Up Development Environment

### Ubuntu 24.04
```bash
sudo apt install python3 python3-pip python3-pytest tox black flake8
sudo apt install clang-format clang++ libc++-dev libc++abi-dev
rustup install nightly
rustup component add --toolchain nightly clippy rustfmt
```

### MacOS
```bash
brew install astyle clang-format flutter gcc go julia kotlin maven nim rust vlang z3
```

### Install Python Dependencies
```bash
pip3 install -e .[test]
```

## Running Tests

```bash
# All tests
pytest

# Specific language
pytest tests/test_transpiler.py -k rust

# Update expected output
export UPDATE_EXPECTED=1
pytest-3 -k cli -v

# Keep generated files for debugging
export KEEP_GENERATED=1
pytest-3 -k some_test -v
```

## Code Quality

```bash
# Lint
ruff check . --exclude tests

# Fix lint issues
ruff check . --exclude tests --fix

# Type check
pyright .
```
