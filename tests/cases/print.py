#!/usr/bin/env python3


import sys

def test_method(fdesc, entry,
            defaultNamedOptArg,
            defaultNamedNotOptArg,
            defaultUnnamedArg,
            is_comment=True):
    return f"{fdesc}, {entry}, {defaultNamedOptArg},{defaultNamedNotOptArg},{defaultUnnamedArg}"

def show():
    print("b")
    print(2, "b")
    a: float = 2.1
    print(a)
    b = 2.1
    print(b)
    c = True
    print(c)
    name = "test"
    val = True
    print(
        "%s_vtables_dispatch_ = %d" % (name, val),
        file=sys.stdout,
    )

    name = "test_method"
    fdesc = "self"
    entry = "some_entry"
    print(
        "#\tdef "
        + name
        + "(self"
        + test_method(
            fdesc,
            entry,
            "defaultNamedOptArg",
            "defaultNamedNotOptArg",
            "defaultUnnamedArg",
            is_comment=True,
        )
        + "):",
        file=sys.stdout,
    )

    indent = 2
    test = "test"
    print(" " * indent, test)


if __name__ == "__main__":
    show()
