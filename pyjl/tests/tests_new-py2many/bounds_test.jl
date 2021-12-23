function main()
seq::Vector{Int64} = [1, 2, 3, 4, 5]
seq_copy::Vector{Int64} = [1, 2, 3, 4, 5]
gap = 1
for i in (0:length(seq) - gap - 1)
@assert(seq[i + 1] == seq_copy[i + 1])
end
complex_list = [([1, 2], 3, 4)]
for ((a1, a2), b, c) in complex_list
@assert(a1 == 1)
@assert(a2 == 2)
@assert(b == 3)
@assert(c == 4)
arr = []
a = 1
for j in (0:1)
push!(arr, a);
a += 1
end
@assert(arr[1] == 1)
@assert(arr[2] == 2)
end
@assert(seq[1] == 1)
@assert(seq[3] == 3)
@assert(seq[end] == 5)
x = 1
@assert(seq[x + 1] == 2)
println("OK");
end

main()
