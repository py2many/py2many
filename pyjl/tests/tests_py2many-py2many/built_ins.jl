function default_builtins()
a = string()
b = false
c = zero(Int)
@assert(a == "")
@assert(b == false)
@assert(c == 0)
end

function main()
default_builtins();
a = max(1, 2)
@assert(a == 2)
b = min(1, 2)
@assert(b == 1)
println("OK");
end

main()
