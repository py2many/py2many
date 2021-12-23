
function test_python(iterations::Int64)
iteration = 0
total = float(0.0)
array_length = 1000
array::Vector{Int64} = [i for i in (0:array_length - 1)]
while iteration < iterations
innerloop = 0
while innerloop < 100
total += array[((iteration + innerloop) % array_length) + 1]
innerloop += 1
end
iteration += 1
end
@assert(total == 15150)
println("OK");
empty!(array)
end

function main()
test_python(3);
end

main()
