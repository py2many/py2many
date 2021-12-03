#!/usr/bin/env python3

from tempfile import NamedTemporaryFile


if __name__ == "__main__":
    with NamedTemporaryFile(mode="a+", delete=False) as temp_file:
        file_path = temp_file.name
        with open(file_path, "w") as f:
            f.write("hello")
        with open(file_path, "r") as f:
            assert f.read(1) == "h"
            assert f.read() == "ello"
            print("OK")
