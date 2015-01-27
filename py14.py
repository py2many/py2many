#!/usr/bin/env python
import sys
import argparse
from py14.transpiler import transpile


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Transpile Python to C++14")
    parser.add_argument("script", metavar='<python file>')
    parser.add_argument('--testing', action='store_true')
    args = parser.parse_args()

    source = open(args.script).read()
    cpp = transpile(source, headers=True, testing=args.testing)
    sys.stdout.write(cpp)
