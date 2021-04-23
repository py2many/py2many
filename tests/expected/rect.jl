
struct Rectangle
    height::Int64
    length::Int64
end

function is_square(self::Rectangle)::Bool
    return self.height == self.length
end

function show()
    r = Rectangle(1, 1)
    @assert(r.is_square())
    r = Rectangle(1, 2)
    @assert(!(r.is_square()))
    h = r.height
    l = r.length
    println(join([h], " "))
    println(join([l], " "))
end

function main()
    show()
end

main()
