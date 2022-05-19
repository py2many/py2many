
abstract type AbstractPacket end
abstract type AbstractRegister end
mutable struct Packet <: AbstractPacket
    val::Float64
end

function __repr__(self::AbstractPacket)::String
    return AbstractPacket(self.val)
end

function __eq__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) == __key(other)
end

function __key(self::AbstractPacket)
    (self.val)
end

mutable struct Register <: AbstractRegister
    PACKET::AbstractPacket
    VALUE::Int64
end

if abspath(PROGRAM_FILE) == @__FILE__
    a = VALUE(Register, 10)
    @assert(is_value(a))
    value(a)
    b = PACKET(Register, Packet(1.3))
    @assert(is_packet(b))
    packet(b)
    println("OK")
end
