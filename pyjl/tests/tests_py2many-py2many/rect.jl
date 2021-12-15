using DataClass
#= This file implements a rectangle class  
=#

@dataclass mutable struct Rectangle
height::Int64
length::Int64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end
function is_square(self::Rectangle)::Bool
return self.height == self.length
end


function show()
r = Rectangle(1, 1)
@assert(is_square(r))
r = Rectangle(1, 2)
@assert(!(is_square(r)))
println(r::height);
println(r::length);
end

function main()
show();
end

main()
