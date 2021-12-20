using Pkg; Pkg.add("JuliaFormatter")
using JuliaFormatter

function format_files(dir)
    options = []
    JuliaFormatter.format(dir)
end

format_files("C:/Users/Miguel Marcelino/Desktop/Tese/Repositories/py2many/pyjl/tests/tests_py2many-py2many")

# Failing
# format_files("C:/Users/Miguel Marcelino/Desktop/Tese/Repositories/py2many/pyjl/tests/tests_new-py2many")