#!/bin/bash
TESTS="tests"

# cd "$PY2MANY_HOME"

# Run Translation tests
sudo ./setup.py install

## Base tests
# py2many --julia=1 "$TESTS/cases" --outdir=../pyjl_tests/cases-py2many

## Python tests
# py2many --julia=1 "$TESTS/cases_py" --outdir=../pyjl_tests/cases_py-py2many

## Performance tests
# py2many --julia=1 "$TESTS/performance_tests" --outdir=../pyjl_tests/performance_tests-py2many

## Pywin tests
py2many --julia=1 "$TESTS/pywin/win32com_" --outdir=../pyjl_tests/pywin-py2many/win32com_


# Run Transpiler Tests
# TODO