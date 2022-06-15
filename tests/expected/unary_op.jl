if abspath(PROGRAM_FILE) == @__FILE__
    a::Int64 = 2
    @assert(~a == -3)
    -1
    +1
end
