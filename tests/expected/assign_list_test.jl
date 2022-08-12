if abspath(PROGRAM_FILE) == @__FILE__
    (a, b, c) = [1, 2, 3]
    @assert(a == 1)
    @assert(b == 2)
    @assert(c == 3)
    pairs_ = [(([2, 3, 4], 5, 6), ([7, 8, 9], 10, 11))]
    for (((x1, y1, z1), v1, m1), ((x2, y2, z2), v2, m2)) in pairs_
        @assert(x1 == 2)
        @assert(y1 == 3)
        @assert(z1 == 4)
        @assert(v1 == 5)
        @assert(m1 == 6)
        @assert(x2 == 7)
        @assert(y2 == 8)
        @assert(z2 == 9)
        @assert(v2 == 10)
        @assert(m2 == 11)
    end
end
