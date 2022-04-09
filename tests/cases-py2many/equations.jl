
function main()
    x::Int64 = 0
    y::Int64 = 0
    @assert(!(x > 2))
    @assert(y < 10)
    @assert((x + 2 * y) == 0)
end

main()
