#!/usr/bin/env python3

def show():
    try:
        raise Exception("foo")
    except Exception as e:
        print("caught")
    finally:
        print("Finally")

    try:
        3/0
    except ZeroDivisionError:
        print("OK")

    try:
        raise Exception("foo")
    except:
        print("Got it")

if __name__ == "__main__":
    show()
