#!/usr/bin/env bash

MODE=$1
shift

# Define the directory path
DIR="common-rust-proj"

# Check if the directory exists
if [ ! -d "$DIR" ]; then
    # If the directory doesn't exist, create a new Cargo library project
    cargo new --bin "$DIR"

    echo "Created new Cargo binary project in $DIR"
fi

# Extract the embedded Cargo.toml content
# Look for lines between ```cargo and ```
# Remove the first 4 characters (e.g., "//! ") from each line
bin_name=$(basename -s .rs "$1")
in_block=0
while IFS= read -r line; do
    case "$line" in *'```cargo'*) in_block=1; continue;; esac
    [ "$in_block" = 1 ] || continue
    case "$line" in *'```'*) break;; esac
    line=${line#//! }    # strip the "//! " doc-comment prefix
    printf '%s\n' "$line"
    [ "$line" = "[package]" ] && printf 'name="%s"\n' "$bin_name"
done < "$1" > "$DIR/Cargo.toml"

# Now copy the argument to the target dir
cp $1 $DIR/src/main.rs
shift;

if [ "$MODE" = "lint" ]; then
    cd $DIR
    # uncomment if there are lint errors py2many didn't fix or was asked not to fix
    #cargo clippy --fix --allow-dirty
    cargo clippy
elif [ "$MODE" = "compile" ]; then
    cargo build --manifest-path $DIR/Cargo.toml
else
    cargo run --manifest-path $DIR/Cargo.toml $*
fi
