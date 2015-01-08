import sys
import os
import contextlib
import ast
import inspect
from subprocess import check_call

from transpiler import CppTranspiler


@contextlib.contextmanager
def working_directory(path):
    """
    A context manager which changes the working directory to the given
    path, and then changes it back to its previous value on exit.
    """
    prev_cwd = os.getcwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(prev_cwd)


class Compiler:
    """
    Compiler takes care of generating the Makefile and C++ Source Code
    """
    def __init__(self, dest="generated"):
        self.dest = dest
        try:
            os.mkdir(dest)
        except OSError:
            pass
        sys.path.append(self.dest)

    @staticmethod
    def python_version():
        info = sys.version_info
        major, minor = info[0], info[1]
        return "{0}.{1}".format(major, minor)

    @staticmethod
    def guess_cpp_types(args):
        for arg in args:
            if arg == int:
                yield "int"
            if arg == str:
                yield "std::string"


    def create_code(self, module_name, cpp_func):
        with open(os.path.join(self.dest, module_name) + ".hpp", 'w') as fh:
            fh.write(cpp_func)

    def create_module(self, module_name, cpp_func, func_name, arg_types):
        arg_types = ",".join(Compiler.guess_cpp_types(arg_types))
        with open(os.path.join(self.dest, module_name) + ".cpp", 'w') as fh:
            fh.write('\n#include "{0}.hpp"\n'.format(module_name))
            fh.write("\n#include <boost/python.hpp>\n")
            fh.write("BOOST_PYTHON_MODULE(" + module_name + ") {\n")
            fh.write("using namespace boost::python;\n")
            fh.write('def("{0}", {0}<{1}>);\n'.format(func_name, arg_types))
            fh.write("}")

    def create_makefile(self, module_name):
        with open(os.path.join(self.dest, "Makefile"), "w") as fh:
            vars = {"CXX": "clang++",
                    "PYTHON_VERSION": Compiler.python_version(),
                    "PYTHON_INCLUDE": "/usr/include/python$(PYTHON_VERSION)",
                    "BOOST_INC": "/usr/include/boost",
                    "BOOST_LIB": "/usr/lib",
                    "TARGET": module_name}
            for var, val in vars.items():
                fh.write("{0} = {1}\n".format(var, val))

            fh.write("$(TARGET).so: $(TARGET).o\n")
            fh.write("\t$(CXX) -std=c++14 -shared "
                     "-Wl,--export-dynamic $(TARGET).o -L$(BOOST_LIB) "
                     "-lboost_python -L/usr/lib/python$(PYTHON_VERSION)/config "
                     "-lpython$(PYTHON_VERSION) -O3 -o $(TARGET).so\n")
            fh.write("$(TARGET).o: $(TARGET).cpp\n")
            fh.write("\t$(CXX) -std=c++14 -I$(PYTHON_INCLUDE) -I$(BOOST_INC) "
                     "-fPIC -c $(TARGET).cpp\n")
            fh.write("clean:\n"
                     "\trm -f *.o *.so")

    def try_clang_format(self, filename):
            try:
                check_call(["clang-format-3.5", "-i", "-style=LLVM", filename])
            except OSError:
                pass

    def compile(self, py_func, args):
        func_name = py_func.__name__
        arg_types = [type(arg) for arg in args]
        source_file = inspect.getsourcefile(py_func)
        tree = ast.parse(inspect.getsource(py_func), filename=source_file)
        cpp_func = CppTranspiler().visit(tree)
        module_name = func_name + "_extern"

        self.create_code(module_name, cpp_func)
        self.create_module(module_name, cpp_func, func_name, arg_types)
        self.create_makefile(module_name)
        with working_directory(self.dest):
            self.try_clang_format(module_name + ".cpp")
            check_call(["make"])
