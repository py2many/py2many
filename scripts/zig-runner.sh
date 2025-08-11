#!/bin/sh

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
    # Two arguments, first is mode, second is test file
    MODE=$1
    shift
    TEST_FILE=$2
else
    echo "Usage: $0 [mode] test_file.zig"
    echo "Modes: run, compile, lint"
    exit 1
fi

# Define the directory path
DIR="tests/build/common-zig-proj"

# Check if the directory exists and is properly set up
if [ ! -d "$DIR" ] || [ ! -f "$DIR/build.zig" ] || [ ! -f "$DIR/build.zig.zon" ]; then
    echo "Zig build environment not found. Running setup..."
    # Call zig-setup.sh to set up the environment
    SCRIPT_DIR="$(dirname "$0")"
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
