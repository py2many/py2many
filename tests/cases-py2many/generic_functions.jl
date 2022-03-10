
function sum_two(x::Int64, y::Int64)::Int64
    return x + y
end

function get_first(container::Vector{Int64})::Int64
    return container[1]
end

function main()
    @assert(sum_two(1, 2) == 3)
    @assert(sum_two(1, convert(Int64, 2.0)) == 3.0)
    @assert(sum_two(convert(Int64, "1"), convert(Int64, "2")) == "12")
    @assert(get_first([1, 2, 3]) == 1)
    @assert(get_first(convert(Vector{Int64}, ["1", "2", "3"])) == "1")
    @assert(get_first(convert(Vector{Int64}, ["1", 2, 3])) == "1")
    @assert(get_first(convert(Vector{Int64}, "123")) == "1")
end

main()
