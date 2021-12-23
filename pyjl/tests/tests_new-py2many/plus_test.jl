function plus_test(x, y)
return x + y
end

function plus_test(x::String, y::String)::String
return x * y
end

function main()
x = "ss"
y = "zz"
res = plus_test(x, y)
@assert(res == "sszz")
println("OK");
end

main()
