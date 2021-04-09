#!/usr/bin/env python3

import os.path
import sys

try:
    project_root = os.path.dirname(__file__)
    sys.path.insert(0, project_root)
except Exception:
    project_root = None

from py2many.cli import main


if __name__ == "__main__":
    main()
