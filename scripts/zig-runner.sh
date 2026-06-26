#!/usr/bin/env bash

# Check if we have at least one argument
if [ $# -eq 0 ]; then
    echo "Usage: $0 [mode] test_file.zig"
    echo "Modes: run (default), compile, lint"
    exit 1
fi

# Parse arguments: an optional leading mode, the test file, then any program
# arguments (forwarded to the program when running, e.g. sys.argv tests).
case "$1" in
    run | compile | lint)
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

# Run from the repo root so every subsequent path (the project dir, the
# zig-setup.sh invocation, etc.) resolves the same way regardless of where the
# caller invoked us from. Make $TEST_FILE absolute first, so a caller-relative
# path keeps pointing at the right file after we cd.
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
TEST_FILE="$(cd "$(dirname "$TEST_FILE")" && pwd)/$(basename "$TEST_FILE")"
cd "$REPO_ROOT"

DIR="tests/build/common-zig-proj"

# Check if the directory exists and is properly set up
if [ ! -d "$DIR" ] || [ ! -f "$DIR/build.zig" ] || [ ! -f "$DIR/build.zig.zon" ]; then
    echo "Zig build environment not found. Running setup..."
    "$SCRIPT_DIR/zig-setup.sh"
fi
PROJ="$REPO_ROOT/$DIR"

# Build in a private per-invocation directory so concurrent runs (pytest-xdist)
# don't clobber each other's src/main.zig or zig-out/bin/test. build.zig and
# build.zig.zon are copied from the shared template; the pylib dependency
# resolves from the shared global cache. The compile cache is shared via
# --cache-dir (zig locks it for safe concurrent access), so the isolation costs
# disk, not recompilation.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/zig-runner.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/src"
cp "$PROJ/build.zig" "$PROJ/build.zig.zon" "$WORK/"
cp "$TEST_FILE" "$WORK/src/main.zig"
CACHE_DIR="$PROJ/.zig-cache"
cd "$WORK"

if [ "$MODE" = "lint" ]; then
    zig fmt src/main.zig
    zig build --cache-dir "$CACHE_DIR"
elif [ "$MODE" = "compile" ]; then
    zig build --cache-dir "$CACHE_DIR"
else
    # Build first, then run the binary directly so that non-zero exit codes
    # from the program are not conflated with zig build failures.
    zig build --cache-dir "$CACHE_DIR" 2>&1
    if [ $? -ne 0 ]; then
        echo "Build failed" >&2
        exit 1
    fi
    ./zig-out/bin/test "${PROG_ARGS[@]}"
fi
