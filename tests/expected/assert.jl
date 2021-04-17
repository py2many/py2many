function compare_assert(a::Int64, b::Int64)
    @assert(a == b)
end

function main()
    compare_assert(1, 1)
end

main()
