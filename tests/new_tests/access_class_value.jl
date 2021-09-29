
# @dataclass
struct Packet
    val::Float64
end


# @dataclass
struct Register
    PACKET::Packet	
    VALUE::Int64
end


function main()
    a = Register(Packet(1.3), 10)
    println(join(["OK"], " "));
end

main()
