
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
    h = r.height
    l = r.length
    println(join([h], " "))
    println(join([l], " "))
end

function main()
    show()
end

main()
