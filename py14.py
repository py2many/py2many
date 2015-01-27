#!/usr/bin/env python
import sys
from py14.transpiler import transpile


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./py14.py <python file>")
        sys.exit(1)

    filename = sys.argv[1]
    source = open(filename).read()
    cpp = transpile(source, headers=True)
    sys.stdout.write(cpp)
