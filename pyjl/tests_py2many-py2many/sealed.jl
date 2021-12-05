using DataClass


@dataclass mutable struct Packet
val::Float64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end


struct Register
PACKET::Packet
VALUE::Int64
end


function main()
a = VALUE(Register, 10)
@assert(is_value(a))
value(a);
b = PACKET(Register, Packet(1.3))
@assert(is_packet(b))
packet(b);
println("OK");
end

main()
