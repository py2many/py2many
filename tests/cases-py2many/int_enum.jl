
abstract type AbstractColors <: AbstractIntEnum end
abstract type AbstractPermissions <: AbstractIntFlag end

struct Colors <: IntEnum
    RED::Any = auto()
    GREEN::Any = auto()
    BLUE::Any = auto()
end



struct Permissions <: IntFlag
    R::Int64 = 1
    W::Int64 = 2
    X::Int64 = 16
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
