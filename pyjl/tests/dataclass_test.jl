
@dataclass
mutable struct ValueHolder
val::Int64
strVal::String
_initvars = [_init=true, _repr=true, _eq=true, _order=true, _unsafe_hash=false, _frozen=false, _create_jl_annotation=true]
end


function main()
a = ValueHolder(10, "1")
println(a);
__init__(ValueHolder, a, 2, "10");
println(a);
end

main()
