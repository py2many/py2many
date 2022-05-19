#= Keywords (from "Grammar/python.gram")

This file is automatically generated; please don't muck it up!

To update the symbols in this file, 'cd' to the top directory of
the python source tree and run:

    PYTHONPATH=Tools/peg_generator python3 -m pegen.keywordgen         Grammar/Grammar         Grammar/Tokens         Lib/keyword.py

Alternatively, you can run 'make regen-keyword'.
 =#
using FunctionalCollections
export iskeyword, issoftkeyword, kwlist, softkwlist
kwlist = ["False", "None", "True", "__peg_parser__", "and", "as", "assert", "async", "await", "break", "class", "continue", "def", "del", "elif", "else", "except", "finally", "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try", "while", "with", "yield"]
softkwlist = []
iskeyword = x::pset, y -> y in x
issoftkeyword = x::pset, y -> y in x