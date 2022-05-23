function string_literals()
    l1 = "literals\a"
    l2 = "literals\b"
    l3 = "literals\f"
    l4 = "literals\n"
    l5 = "literals\r"
    l6 = "literals\v"
    l7 = "literals\t"
    l8 = "+"
    @assert(l8 == "+")
    l9 = "+"
    @assert(l9 == "+")
    m = "literal\n           literal"
    s = "literal"
    t = "literal"
end

function integer_literals()
    l1 = 0b10110
    @assert(l1 == 22)
    l2 = 0o333
    @assert(l2 == 219)
    l3 = 50
    @assert(l3 == 50)
    l4 = 0x14c
    @assert(l4 == 332)
end

function floating_point_literals()
    l1 = 25.99999
    l2 = 26.11111
    l3 = 0.001
    l4 = 10.0
    l5 = 10000000000.0
    l6 = 3.14e-10
    l7 = 3.141593
    @assert(l3 == 0.001)
    @assert(l4 == 10)
    @assert(l5 == 10000000000)
    @assert(l6 == 3.14e-10)
    @assert(l7 == 3.141593)
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

if abspath(PROGRAM_FILE) == @__FILE__
    string_literals()
    integer_literals()
    floating_point_literals()
    imaginary()
    boolean_literals()
end
