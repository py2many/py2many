if abspath(PROGRAM_FILE) == @__FILE__
    a = 2
    @assert(~a == -3)
    -1
    +1
end
