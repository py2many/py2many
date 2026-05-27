#!/usr/bin/env bash

# Check if we have at least one argument
if [ $# -eq 0 ]; then
    echo "Usage: $0 [mode] test_file.zig"
    echo "Modes: run (default), compile, lint"
    exit 1
fi

# Parse arguments - mode is optional and comes first
if [ $# -eq 1 ]; then
    # Only one argument, assume it's the test file
    MODE="run"
    TEST_FILE=$1
elif [ $# -eq 2 ]; then
    # Two arguments: mode then test file. Consume the mode with shift so $* holds
    # the remaining args (the test file, then any program args).
    MODE=$1
    shift
    TEST_FILE=$1
else
    echo "Usage: $0 [mode] test_file.zig"
    echo "Modes: run, compile, lint"
    exit 1
fi

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

# Copy the test file to src/main.zig
cp "$TEST_FILE" "$DIR/src/main.zig"

if [ "$MODE" = "lint" ]; then
    cd "$DIR"
    zig fmt src/main.zig
    zig build
elif [ "$MODE" = "compile" ]; then
    cd "$DIR"
    zig build
else
    cd "$DIR"
    zig run $* 2>&1
fi
