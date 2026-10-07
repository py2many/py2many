#!/usr/bin/env bash

# Verify/run a single generated .lean file with `lean`.
#
# Lean's verification flow: if the file type-checks, its pre/post-conditions
# and invariants (#805) hold -- the equivalent of `py2many --smt file.py |
# z3 -smt2 -in` reporting no counter-example.
#
# `lean` on its own covers both modes: `lean file.lean` type-checks without
# executing anything ("build" mode), and `lean --run file.lean args...`
# type-checks, links, then runs `main`, forwarding program arguments and its
# exit code.
#
# We deliberately don't shell out to `lake`. Lake locates its Lean
# installation from its own executable path, which is unusable in the
# Alpine/gcompat CI image: `/proc/self/exe` resolves to `/bin/busybox` there
# (gcompat's `ld-linux-x86-64.so.2` is busybox), so lake sees sysroot `/` and
# fails with "could not detect the configuration of the Lake installation" --
# no combination of LEAN_PATH/LEAN_SYSROOT/LAKE_HOME rescues it. `lean` only
# needs its stdlib search path (LEAN_PATH) pinned, and the formatter
# (`lean --run pylean/fmt.lean`) needs the same thing anyway.
#
# `lean` comes from the `http:lean` mise tool (MISE_ENV=lean), so this is
# expected to be invoked under `MISE_ENV=lean mise exec -- ...`; it is found
# via the inherited PATH.

if [ $# -eq 0 ]; then
    echo "Usage: $0 [mode] test_file.lean [args...]"
    echo "Modes: run (default, verify then execute), build (verify only)"
    exit 1
fi

# Optional leading mode, then the .lean file, then any program arguments.
case "$1" in
    run | build)
        MODE=$1
        shift
        ;;
    *)
        MODE="run"
        ;;
esac
TEST_FILE=$1
shift
PROG_ARGS=("$@")

# Make the test file absolute before we cd away from the caller's directory.
TEST_FILE="$(cd "$(dirname "$TEST_FILE")" && pwd)/$(basename "$TEST_FILE")"

# Diagnostics go to stderr so stdout carries only the program's own output.
if [ "$MODE" = "run" ]; then
    exec lean --run "$TEST_FILE" ${PROG_ARGS+"${PROG_ARGS[@]}"}
fi
exec lean "$TEST_FILE"
