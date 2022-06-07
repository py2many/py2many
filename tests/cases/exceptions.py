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


if __name__ == "__main__":
    show()
