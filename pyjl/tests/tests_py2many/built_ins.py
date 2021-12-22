#!/usr/bin/env python3

def default_builtins():
    a = str()
    b = bool()
    c = int()
    assert a == ""
    assert b == False
    assert c == 0

if __name__ == "__main__":
    default_builtins()

    a = max(1, 2)
    assert a == 2
    b = min(1, 2)
    assert b == 1

    print("OK")
