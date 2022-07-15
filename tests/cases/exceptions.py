#!/usr/bin/env python3


def show():
    s = []
    try:
        raise Exception("foo")
    except Exception as e:
        s.append("foo")
    finally:
        s.append("Finally")

    try:
        3 / 0
    except ZeroDivisionError:
        s.append("ZeroDivisionError")

    try:
        raise Exception("foo")
    except:
        s.append("foo_2")

    return s

    try:
        raise Exception("foo")
    except Exception as e:
        assert "foo" in str(e)


if __name__ == "__main__":
    assert show() == ["foo", "Finally", "ZeroDivisionError", "foo_2"]
