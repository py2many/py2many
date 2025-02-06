#!/bin/sh
#
MODE=$1
shift

if [ "$MODE" = "lint" ]; then
    # run ziglint?
    true
elif [ "$MODE" = "compile" ]; then
    zig build $*
else
    zig run $* 2>&1
fi
