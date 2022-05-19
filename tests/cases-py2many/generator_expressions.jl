if abspath(PROGRAM_FILE) == @__FILE__
    value = join((string(x) for x in 0:9 if x > 4 && x < 8), " ")
    @assert(value == "5 6 7")
    value2 = join((string(x) * " " * string(y) for x in 0:4 if x > 1 for y = 0:1), " ")
    @assert(value2 == "2 0 2 1 3 0 3 1 4 0 4 1")
    value3 = join((string(x + y) for x in 0:4 if x > 1 for y = 0:3), " ")
    @assert(value3 == "2 3 4 5 3 4 5 6 4 5 6 7")
end
