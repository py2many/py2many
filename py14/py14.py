#!/usr/bin/env python
import sys
from transpiler import transpile


if __name__ == "__main__":
    filename = sys.argv[1]
    source = open(filename).read()
    cpp = transpile(source, headers=True)
    print(cpp)
