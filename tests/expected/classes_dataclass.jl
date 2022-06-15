
abstract type AbstractPacket end
abstract type AbstractRegister end
abstract type AbstractValueHolder end
mutable struct Packet <: AbstractPacket
    val::Float64
end

function __repr__(self::AbstractPacket)::String
    return AbstractPacket(self.val)
end


function __eq__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) == __key(other)
end


function __lt__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) < __key(other)
end

function __le__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) <= __key(other)
end

function __gt__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) > __key(other)
end

function __ge__(self::AbstractPacket, other::AbstractPacket)::Bool
    return __key(self) >= __key(other)
end


function __key(self::AbstractPacket)
    (self.val)
end

mutable struct Register <: AbstractRegister
    PACKET::AbstractPacket
    VALUE::Int64
end

function __repr__(self::AbstractRegister)::String
    return AbstractRegister(self.PACKET, self.VALUE)
end


function __eq__(self::AbstractRegister, other::AbstractRegister)::Bool
    return __key(self) == __key(other)
end


function __lt__(self::AbstractRegister, other::AbstractRegister)::Bool
    return __key(self) < __key(other)
end

function __le__(self::AbstractRegister, other::AbstractRegister)::Bool
    return __key(self) <= __key(other)
end

function __gt__(self::AbstractRegister, other::AbstractRegister)::Bool
    return __key(self) > __key(other)
end

function __ge__(self::AbstractRegister, other::AbstractRegister)::Bool
    return __key(self) >= __key(other)
end


function __key(self::AbstractRegister)
    (__key(self.PACKET), self.VALUE)
end

mutable struct ValueHolder <: AbstractValueHolder
    val::Int64
    strVal::String
end

function __repr__(self::AbstractValueHolder)::String
    return AbstractValueHolder(self.val, self.strVal)
end


function __eq__(self::AbstractValueHolder, other::AbstractValueHolder)::Bool
    return __key(self) == __key(other)
end


function __lt__(self::AbstractValueHolder, other::AbstractValueHolder)::Bool
    return __key(self) < __key(other)
end

function __le__(self::AbstractValueHolder, other::AbstractValueHolder)::Bool
    return __key(self) <= __key(other)
end

function __gt__(self::AbstractValueHolder, other::AbstractValueHolder)::Bool
    return __key(self) > __key(other)
end

function __ge__(self::AbstractValueHolder, other::AbstractValueHolder)::Bool
    return __key(self) >= __key(other)
end


function __key(self::AbstractValueHolder)
    (self.val, self.strVal)
end

if abspath(PROGRAM_FILE) == @__FILE__
    c1 = ValueHolder(10, "10")
    @assert(__eq__(c1, ValueHolder(10, "10")))
    c2 = ValueHolder(10, "10")
    @assert(__le__(c1, c2))
    @assert(__ge__(c1, c2))
    c1 = ValueHolder(11, "10")
    @assert(__lt__(c2, c1))
    @assert(__gt__(c1, c2))
    c3 = Packet(2.4)
    @assert(__eq__(c3, Packet(2.4)))
    c4 = Packet(2.4)
    @assert(__le__(c3, c4))
    @assert(__ge__(c3, c4))
    c3 = Packet(2.5)
    @assert(__lt__(c4, c3))
    @assert(__gt__(c3, c4))
    c5 = Register(Packet(2.2), 10)
    @assert(__eq__(c5, Register(Packet(2.2), 10)))
    c6 = Register(Packet(2.2), 10)
    @assert(__le__(c5, c6))
    @assert(__ge__(c5, c6))
    c5 = Register(Packet(2.3), 10)
    @assert(__lt__(c6, c5))
    @assert(__gt__(c5, c6))
end
