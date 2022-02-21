#= This file implements a rectangle class  
=#

abstract type AbstractRectangle end
mutable struct Rectangle <: AbstractRectangle
    height::Int64
    length::Int64
end
function is_square(self::AbstractRectangle)::Bool
    return self.height == self.length
end

function __init__(self::Rectangle, height::Int64, length::Int64)
    setfield!(self::Rectangle, :height, height::Int64)
    setfield!(self::Rectangle, :length, length::Int64)

end

function __repr__(self::Rectangle)::String
    return Rectangle(
        getfield!(self::Rectangle, height::Int64),
        getfield!(self::Rectangle, length::Int64),
    )
end
function __eq__(self::Rectangle, other::Rectangle)::Bool
    return __key(self) == __key(other)
end

function __key(self::Rectangle)
    (getfield!(self::Rectangle, height::Int64), getfield!(self::Rectangle, length::Int64))
end


function show()
    r = Rectangle(1, 1)
    @assert(is_square(r))
    r = Rectangle(1, 2)
    @assert(!(is_square(r)))
    println(height(r))
    println(length(r))
end

function main()
    show()
end

main()
