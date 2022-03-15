
abstract type AbstractPacket end
abstract type AbstractRegister end

mutable struct Packet <: AbstractPacket

end

                function __init__(self::AbstractPacket, )
                    setfield!(self::AbstractPacket, :, )
                end
            

                function __repr__(self::AbstractPacket)::String 
                    return AbstractPacket(self.) 
                end
            

                function __eq__(self::AbstractPacket, other::AbstractPacket)::Bool
                    return __key(self) == __key(other)
                end
            

                function __key(self::AbstractPacket)
                    (self.)
                end
                
mutable struct Register <: AbstractRegister

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
