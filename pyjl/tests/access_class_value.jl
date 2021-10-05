using DataClass

@dataclass
mutable struct Packet
val::Float64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end


@dataclass
mutable struct Register
PACKET::Packet
VALUE::Int64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end


function main()
a = Register(Packet(1.3), 10)
println("OK");
end

main()
