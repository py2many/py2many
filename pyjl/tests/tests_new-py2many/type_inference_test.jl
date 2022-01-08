
function fibonacci(n)::Int64
if n == 0
return 0
elseif n == 1
return 1
else
return fibonacci(n - 2) + fibonacci(n - 1)
end
end

function mul_list()::Int64
a::Vector = []
for i in (0:4)
push!(a, i);
end
return repeat(a,2)
end

function combinations(array)::Vector
result = []
for x in array
for y in array
push!(result, (x, y));
end
end
return result
end

function mul_recvd_list(a)::Int64
for i in (0:4)
append(a, i);
end
return 2*a
end

function main()
@assert(fibonacci(10) == 55)
@assert((repeat("ola",fibonacci(3))) == "olaola")
a = []
a_mul = mul_recvd_list(a)
println(a_mul);
println("OK");
end

main()
