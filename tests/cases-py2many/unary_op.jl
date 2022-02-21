function bitwise_not_int()::Int64
    a::Int64 = 2
    return ~a
end

function main()
    @assert(bitwise_not_int() == -3)
    -1
end

main()
