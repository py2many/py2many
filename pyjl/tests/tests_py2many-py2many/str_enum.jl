abstract type AbstractColors end

struct Colors::str, Enum, AbstractColors 
end

function show()
color_map = Dict(Colors.RED => "1", Colors.GREEN => "2", Colors.BLUE => "3")
a = Colors.GREEN
if a == Colors.GREEN
println("green");
else
println("Not green");
end
println(length(color_map));
end

function main()
show();
end

main()
