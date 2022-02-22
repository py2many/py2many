function string_literals()
    l1 = "literals"
    l2 = "literals"
    l3 = "literals"
    l4 = "literals\n"
    l5 = "literals"
    l6 = "literals"
    l7 = "literals	"
    l8 = "+"
    @assert(l8 == "+")
    l9 = "+"
    @assert(l9 == "+")
    m = "literal\n           literal"
    s = "literal"
    t = "literal"
end

function integer_literals()
    l1 = 22
    @assert(l1 == 22)
    l2 = 219
    @assert(l2 == 219)
    l3 = 50
    @assert(l3 == 50)
    l4 = 332
    @assert(l4 == 332)
end

function floating_point_literals()
    l1 = 25.99999
    l2 = 26.11111
end

function imaginary()
    l1 = 5im
end

function boolean_literals()
    l1 = 1 == true
    l2 = 1 == false
    l3 = true + l1
    l4 = false + l2
    @assert(l1 == 1)
    @assert(l2 == 0)
    @assert(l3 == 2)
    @assert(l4 == 0)
end

function main()
    string_literals()
    integer_literals()
    floating_point_literals()
    imaginary()
    boolean_literals()
end

main()
