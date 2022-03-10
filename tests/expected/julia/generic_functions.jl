
function sum_two(x, y)
    return x + y
end

function get_first(container)
    return container[1]
end

function main()
    @assert(sum_two(1, 2) == 3)
    @assert(sum_two(1, 2.0) == 3.0)
    @assert(sum_two("1", "2") == "12")
    @assert(get_first([1, 2, 3]) == 1)
    @assert(get_first(["1", "2", "3"]) == "1")
    @assert(get_first(["1", 2, 3]) == "1")
    @assert(get_first("123") == "1")
end

main()
