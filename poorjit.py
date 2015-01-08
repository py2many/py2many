#!/usr/bin/env python
from collections import Counter

from compiler import Compiler


class Recorder:
    """
    A recorder wraps around a function and records the types of the
    parameters passed.
    It keeps track of all passed type combinations.
    """
    calls = Counter()

    def record(self, *args, **kw):
        call = tuple([type(arg) for arg in args])
        self.calls[call] += 1

    def __repr__(self):
        return self.calls.__repr__()


def cpp(py_func):
    """
    Transpiles code of function into C++, compiles it and reimports
    it as extern function.
    The first time the function is invoked we look at the types of
    the parameters and create compile a C++ function for subsequent
    usages.
    Could recompile different versions for different types
    """
    recorder = Recorder()
    compiler = Compiler()

    def try_import_execute(*args):
        func_name = py_func.__name__
        extern_module = __import__(func_name + "_extern")
        extern_func = getattr(extern_module, func_name)
        return extern_func(*args)

    def wrapper(*args):
        recorder.record(*args)
        try:
            return try_import_execute(*args)
        except ImportError:
            compiler.compile(py_func, args)
            return try_import_execute(*args)

    return wrapper
