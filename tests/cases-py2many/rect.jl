#= This file implements a rectangle class  
=#

abstract type AbstractRectangle end
mutable struct Rectangle <: AbstractRectangle

end
function is_square(self::AbstractRectangle)::Bool
return self.height == self.length
end


                function __init__(self::AbstractRectangle, )
                    setfield!(self::AbstractRectangle, :, )
                end
            

                function __repr__(self::AbstractRectangle)::String 
                    return AbstractRectangle(self.) 
                end
            

                function __eq__(self::AbstractRectangle, other::AbstractRectangle)::Bool
                    return __key(self) == __key(other)
                end
            

                function __key(self::AbstractRectangle)
                    (self.)
                end
                
function show()
r = Rectangle(1, 1)
@assert(is_square(r))
r = Rectangle(1, 2)
@assert(!is_square(r))
println(height(r))
println(length(r))
end

function main()
show()
end

main()
