struct Packet
    val::Float64
end

struct Register
    PACKET::Packet
    VALUE::Int64
end

PACKET::Packet = None
VALUE::Int64 = None

function main()
    a = VALUE(Register, 10)
    @assert(is_value(a))
    value(a);
    b = PACKET(Register, Packet(1.3))
    @assert(is_packet(b))
    packet(b);
    println(join(["OK"], " "));
end

main()
