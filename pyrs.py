#!/usr/bin/env python
import sys
import argparse
from pyrs.transpiler import transpile


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Transpile Python to Rust")
    parser.add_argument("script", metavar='<python file>')
    parser.add_argument('--testing', action='store_true')
    args = parser.parse_args()

    source = open(args.script).read()
    rs = transpile(source, headers=True, testing=args.testing)
    sys.stdout.write(rs)
