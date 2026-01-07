#!/usr/bin/env python3


class MockFile:
    def __init__(self, name):
        self.name = name
        self.closed = False

    def __enter__(self):
        print(f"Opening {self.name}")
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        print(f"Closing {self.name}")
        self.closed = True
        return False

    def read(self):
        return "content"


def show():
    # Test with statement
    with MockFile("test.txt") as f:
        print(f.read())


if __name__ == "__main__":
    show()
