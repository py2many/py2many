
abstract type AbstractColors <: AbstractIntEnum end
abstract type AbstractPermissions <: AbstractIntFlag end
mutable struct Colors <: AbstractColors
    RED::Any
    GREEN::Any
    BLUE::Any

    Colors(RED::Any = auto(), GREEN::Any = auto(), BLUE::Any = auto()) =
        new(RED, GREEN, BLUE)
end

mutable struct Permissions <: AbstractPermissions
    X::Int64
    W::Int64
    R::Int64

    Permissions(X::Int64 = 16, W::Int64 = 2, R::Int64 = 1) = new(X, W, R)
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
