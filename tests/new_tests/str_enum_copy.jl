using PyEnum

@pyenum Colors begin
	RED
	GREEN
	BLUE
end
function show()
color_map = Dict(Colors.RED => "1", Colors.GREEN => "2", Colors.BLUE => "3")
a = Colors.GREEN
if a == Colors.GREEN
println(join(["green"], " "));
else

println(join(["Not green"], " "));
end
println(join([length(color_map)], " "));
end

function main()
show();
end

main()
