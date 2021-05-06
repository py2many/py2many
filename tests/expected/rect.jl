# This file implements a rectangle class 

struct Rectangle
    height::Int64
    length::Int64
end

function is_square(self::Rectangle)::Bool
    return self.height == self.length
end

function show()
    r = Rectangle(1, 1)
    @assert(is_square(r))
    r = Rectangle(1, 2)
    @assert(!(is_square(r)))
    println(join([r.height], " "))
    println(join([r.length], " "))
end

function main()
    show()
end

main()
