using Dataclass

@dataclass mutable struct ValueHolder
val::Int64
strVal::String
_initvars = [_init=true, _repr=true, _eq=true, _order=true, _unsafe_hash=false, _frozen=false]
end


function main()
a = ValueHolder(10, "1")
println(a);
__init__(a, 2, "10");
println(a);
end

main()
