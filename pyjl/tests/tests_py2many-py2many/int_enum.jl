
abstract type AbstractColors <: AbstractIntEnum end
abstract type AbstractPermissions <: AbstractIntFlag end
struct Colors <: AbstractColors 
end

struct Permissions <: AbstractPermissions 
end

function show()
color_map = Dict(RED(Colors) => "red", GREEN(Colors) => "green", BLUE(Colors) => "blue")
a = GREEN(Colors)
if a == GREEN(Colors)
println("green");
else
println("Not green");
end
b = R(Permissions)
if b == R(Permissions)
println("R");
else
println("Not R");
end
@assert(length(color_map) != 0)
end

function main()
show();
end

main()
