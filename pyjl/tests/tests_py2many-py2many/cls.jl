abstract type AbstractFoo end
struct Foo::AbstractFoo 
end
function bar(self::Foo)::String
return "a"
end

function main()
f = Foo()
b = bar(f)
@assert(b == "a")
println("OK");
end

main()
