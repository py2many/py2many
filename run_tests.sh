#!/bin/bash
TESTS="tests"

# cd "$PY2MANY_HOME"

# Run Translation tests
sudo ./setup.py install

## Base tests
py2many --julia=1 "$TESTS/cases" --expected "$TESTS/expected/julia"

## Python tests
py2many --julia=1 "$TESTS/cases_py"

## Performance tests
py2many --julia=1 "$TESTS/performance_tests"


# Run Transpiler Tests
# TODO