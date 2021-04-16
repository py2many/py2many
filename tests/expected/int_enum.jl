
struct Colors
RED::ST0
GREEN::ST1
BLUE::ST2
end

RED = auto()
GREEN = auto()
BLUE = auto()
struct Permissions
R::ST0
W::ST1
X::ST2
end

R = 1
W = 2
X = 16
function show()
color_map = [(Colors::RED, "red"), (Colors::GREEN, "green"), (Colors::BLUE, "blue")].iter().cloned().collect::<HashMap<_,_>>()
a = Colors::GREEN
if a == Colors::GREEN
println(join(["green"], " "))
else

println(join(["Not green"], " "))
end
b = Permissions::R
if b == Permissions::R
println(join(["R"], " "))
else

println(join(["Not R"], " "))
end
end

function main()
show()
end

main()

