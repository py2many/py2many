
function test()::Int64
a::Vector{Int64} = [1, 2, 3]
return a[2]
end

function main()
b = test()
@assert(b == 2)
println("OK");
end

main()
