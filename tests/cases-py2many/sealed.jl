

abstract type AbstractPacket end
abstract type AbstractRegister end
mutable struct Packet <: AbstractPacket
    val::Float64
end

function __init__(self::Packet, val::Float64)
    setfield!(self::Packet, :val, val::Float64)

end

function __repr__(self::Packet)::String
    return Packet(getfield!(self::Packet, val::Float64))
end
function __eq__(self::Packet, other::Packet)::Bool
    return __key(self) == __key(other)
end

function __key(self::Packet)
    (getfield!(self::Packet, val::Float64))
end


struct Register <: AbstractRegister
    PACKET::Packet
    VALUE::Int64
end

function main()
    a = VALUE(Register, 10)
    @assert(is_value(a))
    value(a)
    b = PACKET(Register, Packet(1.3))
    @assert(is_packet(b))
    packet(b)
    println("OK")
end

main()
