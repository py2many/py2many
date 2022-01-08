using DataClass

@dataclass mutable struct ValueHolder
val::Int64
strVal::String
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end

@dataclass mutable struct Item
id::String
price_per_unit::Float64
quantity::Int64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end

function main()
a = ValueHolder(10, "1")
println(a);
__init__(a, 2, "10");
println(a);
end

main()
