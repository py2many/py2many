using PyEnum

@pyenum Colors::Int64 begin
    RED
    GREEN
    BLUE
end
@pyenum Permissions::Int64 begin
    R
    W
    X
end
function show()
    color_map = Dict(Colors.RED => "red", Colors.GREEN => "green", Colors.BLUE => "blue")
    a = Colors.GREEN
    if a == Colors.GREEN
        println("green")
    else

        println("Not green")


    end
    b = Permissions.R
    if b == Permissions.R
        println("R")
    else

        println("Not R")


    end
    @assert(length(color_map) != 0)
end

function main()
    show()
end

main()
