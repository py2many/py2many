function plus_test{T0, T1}(x::T0, y::T1)
return (x + y)
end

function plus_test(x::String, y::String)::String
return (x + y)
end

function main()
x = "ss"
y = "zz"
res = plus_test(x, y)
println(res);
end

main()
