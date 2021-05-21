#!/usr/bin/env python3

import tempfile


if __name__ == '__main__':
    with tempfile.NamedTemporaryFile(mode="w") as tmp:
        with open(tmp.name, "w") as f:
            f.write("hello")
        with open(tmp.name, "r") as f:
            print(f.read())
