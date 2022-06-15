function compare_assert(a::Int64, b::Int64)
    @assert(a == b)
    @assert(!(0 == 1))
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(true)
    @assert(!false)
    compare_assert(1, 1)
    @assert(true)
    @assert(true)
    println("OK")
end
