# This file implements a rectangle class 

struct Rectangle
    height::Int
    length::Int
end

function is_square(self)::Bool
    # Go likes this to be camel case
    return self.height == self.length
end

function show()
    r = Rectangle(height = 1, length = 1)
    @assert(is_square(r))
    r = Rectangle(height = 1, length = 2)
    @assert(!(is_square(r)))
    println(r.height)
    println(r.length)
end

function main()
    show()
end

main()
