
abstract type AbstractColors <: AbstractIntEnum end
abstract type AbstractPermissions <: AbstractIntFlag end

struct Colors <: IntEnum
    RED::Any
    GREEN::Any
    BLUE::Any
end
function Colors(RED::Any = auto(), GREEN::Any = auto(), BLUE::Any = auto())::Colors
    return Colors(RED, GREEN, BLUE)
end



struct Permissions <: IntFlag
    R::Int64
    W::Int64
    X::Int64
end
function Permissions(R::Any = 1, W::Any = 2, X::Any = 16)::Permissions
    return Permissions(R, W, X)
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
