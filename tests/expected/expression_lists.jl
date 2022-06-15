
function expression_list()
    a = (1, 2)
    b = (7 * 8, 5 - 6)
    c = (1, 2)
    @assert(a == (1, 2))
    @assert(b == (56, -1))
    @assert(c == (1, 2))
    @assert((a, 4) == ((1, 2), 4))
    @assert(isa(a, Tuple))
end

function starred_item()
    (a, b..., c) = 0:5
    @assert(a == 0)
    @assert(b == [1, 2, 3, 4])
    @assert(c == 5)
    @assert(Dict("x" => 1, Dict("y" => 2)...) == Dict("x" => 1, "y" => 2))
    @assert([0:3..., 4] == [0, 1, 2, 3, 4])
    @assert(Set([0:3..., 4]) == Set([0, 1, 2, 3, 4]))
end

function starred_list()
    n = [1, 2, 3, 4]
    @assert([n..., 5, 6] == [1, 2, 3, 4, 5, 6])
    @assert(([1]..., [2]..., 3) == (1, 2, 3))
    @assert(([1, 2, 3]..., 4 * 1, 5) == (1, 2, 3, 4, 5))
end

if abspath(PROGRAM_FILE) == @__FILE__
    expression_list()
    starred_item()
    starred_list()
end
