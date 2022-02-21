# TODO: Define later (Get from cli)
def transpile(source):
    pass

def parse(*args):
    return "\n".join(args)

def test_print_program_args():
    source = parse(
        'if __name__ == "__main__":', "    for arg in sys.argv:", "       print(arg)"
    )
    cpp = transpile(source)
    # Note the args and return type are missing here as this `transpile` wrapper
    # is not the main py2many wrapper, and notably doesnt use PythonMainRewriter.
    assert cpp == parse(
        "void main() {",
        "pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);",
        "for(auto arg : pycpp::sys::argv) {",
        "std::cout << arg;",
        "std::cout << std::endl;",
        "}}",
        "",
    )