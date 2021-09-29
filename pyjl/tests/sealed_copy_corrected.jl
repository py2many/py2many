# Not fully corrected since it does not fulfil the behaviour of sealed classes
struct Packet
    val::Float64
end


mutable struct Register
    PACKET::Packet
    VALUE::Int64
end

function main()
    
    a = Register(Packet(1.0), 2.0)
    # a = VALUE(Register, 10)
    setfield!(a, :VALUE, 10)
    # @assert(is_value(a))
    # value(a);
    # b = PACKET(Register, Packet(1.3))
    setfield!(a, :PACKET, Packet(1.3))
    # @assert(is_packet(b))
    # packet(b);
    println(join(["OK"], " "));
end

main()
