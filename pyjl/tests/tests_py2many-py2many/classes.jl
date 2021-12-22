struct Foo
end
function bar(self::Foo)::Int64
return baz(self)
end

function baz(self::Foo)::Int64
return 10
end

function main()
f = Foo()
b = bar(f)
@assert(b == 10)
println("OK");
end

main()
