
if abspath(PROGRAM_FILE) == @__FILE__
    x = 0
    y = 0
    @assert(!(x > 2))
    @assert(y < 10)
    @assert((x + 2 * y) == 0)
end
