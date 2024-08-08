#!/usr/bin/env python3


CODE_0 = 0
CODE_1 = 1

CODE_A = "a"
CODE_B = "b"

L_B = {CODE_A}

L_C = {CODE_B: CODE_0}

if __name__ == "__main__":
    assert "a" in L_B
    # Dereferencing items in the dict fails on Rust.
    # Dict compare 'in' does not work on Dart
    # Print of sets and dicts fails on Rust
    print("OK")
