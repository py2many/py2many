#!/usr/bin/env python
import sys
from transpiler import transpile


if __name__ == "__main__":
    filename = sys.argv[1]
    source = open(filename).read()
#    import ipdb; ipdb.set_trace()
    cpp = transpile(source)
    print('#include "sys.h"')
    print('#include "builtins.h"')
    print('#include <iostream>')
    print('#include <string>')
    print('#include <vector>')
    print('#include <utility>')
    print(cpp)
