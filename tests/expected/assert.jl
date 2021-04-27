function compare_assert(a::Int64, b::Int64)
    @assert(a == b)
    @assert(!(0 == 1))
end

function main()
    compare_assert(1, 1)
end
