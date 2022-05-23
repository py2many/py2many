using PyEnum

abstract type AbstractColors <: AbstractIntEnum end
abstract type AbstractPermissions <: AbstractIntFlag end
@pyenum Colors::Int64 begin
    RED = 0
    GREEN = 1
    BLUE = 2
end
@pyenum Permissions::Int64 begin
    R = 1
    W = 2
    X = 16
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

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
