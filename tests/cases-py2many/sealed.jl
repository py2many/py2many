

abstract type AbstractPacket end
abstract type AbstractRegister end
mutable struct Packet <: AbstractPacket
    val::Float64
end

function __init__(self::AbstractPacket, val::Float64)
    setfield!(self::AbstractPacket, :val, val::Float64)
end

function __repr__(self::AbstractPacket)::String
    return AbstractPacket(self.val)
end
function __eq__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) == __key(other)
end

function __key(self::AbstractPacket)
    (__key(self.val))
end


struct Register <: AbstractRegister
    PACKET::AbstractPacket
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
