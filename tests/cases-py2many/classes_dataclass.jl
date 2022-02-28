
abstract type AbstractPacket end
abstract type AbstractRegister end
abstract type AbstractValueHolder end
abstract type AbstractItem end
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


mutable struct Register <: AbstractRegister
    PACKET::Packet
    VALUE::Int64
end

function __init__(self::Register, PACKET::Packet, VALUE::Int64)
    setfield!(self::Register, :PACKET, PACKET::Packet)
    setfield!(self::Register, :VALUE, VALUE::Int64)

end

function __repr__(self::Register)::String
    return Register(
        getfield!(self::Register, PACKET::Packet),
        getfield!(self::Register, VALUE::Int64),
    )
end
function __eq__(self::Register, other::Register)::Bool
    return __key(self) == __key(other)
end

function __key(self::Register)
    (getfield!(self::Register, PACKET::Packet), getfield!(self::Register, VALUE::Int64))
end


mutable struct ValueHolder <: AbstractValueHolder
    val::Int64
    strVal::String
end

function __init__(self::ValueHolder, val::Int64, strVal::String)
    setfield!(self::ValueHolder, :val, val::Int64)
    setfield!(self::ValueHolder, :strVal, strVal::String)

end

function __repr__(self::ValueHolder)::String
    return ValueHolder(
        getfield!(self::ValueHolder, val::Int64),
        getfield!(self::ValueHolder, strVal::String),
    )
end
function __eq__(self::ValueHolder, other::ValueHolder)::Bool
    return __key(self) == __key(other)
end

function __lt__(self::ValueHolder, other::ValueHolder)::Bool
    return __key(self) < __key(other)
end

function __le__(self::ValueHolder, other::ValueHolder)::Bool
    return __key(self) <= __key(other)
end

function __gt__(self::ValueHolder, other::ValueHolder)::Bool
    return __key(self) > __key(other)
end

function __ge__(self::ValueHolder, other::ValueHolder)::Bool
    return __key(self) >= __key(other)
end

function __key(self::ValueHolder)
    (getfield!(self::ValueHolder, val::Int64), getfield!(self::ValueHolder, strVal::String))
end


mutable struct Item <: AbstractItem
    id::String
    price_per_unit::Float64
    quantity::Int64
end

function __init__(self::Item, id::String, price_per_unit::Float64, quantity::Int64)
    setfield!(self::Item, :id, id::String)
    setfield!(self::Item, :price_per_unit, price_per_unit::Float64)
    setfield!(self::Item, :quantity, quantity::Int64)

end

function __repr__(self::Item)::String
    return Item(
        getfield!(self::Item, id::String),
        getfield!(self::Item, price_per_unit::Float64),
        getfield!(self::Item, quantity::Int64),
    )
end
function __eq__(self::Item, other::Item)::Bool
    return __key(self) == __key(other)
end

function __key(self::Item)
    (
        getfield!(self::Item, id::String),
        getfield!(self::Item, price_per_unit::Float64),
        getfield!(self::Item, quantity::Int64),
    )
end


function main()
    a = ValueHolder(10, "1")
    @assert(a == ValueHolder(10, "1"))
    __init__(a, 2, "10")
    @assert(a == ValueHolder(2, "10"))
    a = Register(Packet(1.3), 10)
end

main()
