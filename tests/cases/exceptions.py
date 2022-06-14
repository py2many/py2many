#!/usr/bin/env python3


def show():
    try:
        raise Exception("foo")
    except Exception as e:
        print("caught")
    finally:
        print("Finally")

    try:
        raise Exception("foo")
    except:
        print("Got it")

    try:
        raise Exception("foo")
    except Exception as e:
        assert "foo" in str(e)


if __name__ == "__main__":
    show()
