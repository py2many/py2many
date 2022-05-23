#= This file implements a rectangle class  =#

abstract type AbstractRectangle end
mutable struct Rectangle <: AbstractRectangle
    height::Int64
    length::Int64
end
function is_square(self::Rectangle)::Bool
    #= Go likes this to be camel case =#
    return self.height == self.length
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
    @assert(!is_square(r))
    println(r.height)
    println(r.length)
end

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
