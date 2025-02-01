#!/bin/sh

MODE=$1
shift


# Determine the correct sed command
if [[ "$(uname)" == "Darwin" ]]; then
    # macOS: Use gsed
    SED="gsed"
else
    # Linux/Other: Use sed
    SED="sed"
fi

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
$SED -n '/```cargo/,/```/p' "$1" | $SED '1d;$d' | $SED 's#^//!##' | $SED 's/^ //' > $DIR/Cargo.toml
bin_name=$(basename -s .rs $1)
$SED -i "s/^.package.\$/[package]\nname=\"$bin_name\"/" $DIR/Cargo.toml

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
