#!/usr/bin/env python3


if __name__ == "__main__":
    # byte literals
    assert b"foo" != b"bar"
    assert b'"' == b'"'
    assert b"'" == b"'"
    assert b"\xBBfoo" == b"\xBBfoo"
    print("OK")
