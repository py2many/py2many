# using Pkg;
# Pkg.add("JuliaFormatter");
using JuliaFormatter

function format_files(dir)
    options = []
    JuliaFormatter.format(dir)
end

function receive_files()
    file_name = append!([PROGRAM_FILE], ARGS)[2]
    format_files(file_name)
end

receive_files()
