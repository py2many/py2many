using SuperEnum

abstract type AbstractColors <: IntEnum end
abstract type AbstractPermissions <: IntFlag end
@se Colors::Int64 begin end
@se Permissions::Int64 begin end
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
