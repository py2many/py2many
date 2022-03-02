#= This file implements a rectangle class  
=#
abstract type AbstractRectangle end


mutable struct Rectangle <: AbstractRectangle
    height::Int64
    length::Int64
end
function is_square(self)::Bool
    return self.height == self.length
end


function __init__(self::AbstractRectangle, height::Int64, length::Int64)
    setfield!(self::AbstractRectangle, :height, height::Int64),
    setfield!(self::AbstractRectangle, :length, length::Int64)
end


function __repr__(self::AbstractRectangle)::String
    return AbstractRectangle(self.height, self.length)
end


function __eq__(self::AbstractRectangle, other::AbstractRectangle)::Bool
    return __key(self) == __key(other)
end


function __key(self::AbstractRectangle)
    (self.height, self.length)
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
