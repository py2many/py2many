#!/usr/bin/env bash

# Build/run a single generated .lean file through `lake build`.
#
# Lean's verification flow: if `lake build` succeeds the file type-checks, which
# means its pre/post-conditions and invariants (#805) hold -- the equivalent of
# `py2many --smt file.py | z3 -smt2 -in` reporting no counter-example.
#
# `lean` and `lake` come from the `http:lean` mise tool (MISE_ENV=lean), so this
# is expected to be invoked under `MISE_ENV=lean mise exec -- ...`; lake is found
# via the inherited PATH.

if [ $# -eq 0 ]; then
    echo "Usage: $0 [mode] test_file.lean [args...]"
    echo "Modes: run (default, build then execute), build (verify only)"
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

# Build in a private per-invocation lake project so concurrent runs
# (pytest-xdist) don't clobber a shared Main.lean or .lake build output.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/lean-runner.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
cat > "$WORK/lakefile.toml" <<'EOF'
name = "verify"
defaultTargets = ["verify"]

[[lean_exe]]
name = "verify"
root = "Main"
EOF
cp "$TEST_FILE" "$WORK/Main.lean"
cd "$WORK"

# Build noise goes to stderr so stdout carries only the program's own output.
if ! lake build 1>&2; then
    echo "Build failed" >&2
    exit 1
fi

# "build" mode is verify-only (a successful build is the proof). "run" also
# executes the binary directly so its exit code isn't conflated with lake's.
if [ "$MODE" = "run" ]; then
    ./.lake/build/bin/verify "${PROG_ARGS[@]}"
fi
