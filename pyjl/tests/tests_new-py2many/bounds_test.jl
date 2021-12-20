function main()
seq::Vector{Int64} = [1, 2, 3, 4, 5]
seq_copy::Vector{Int64} = [1, 2, 3, 4, 5]
gap = 1
for i in (0:(length(seq) - gap) - 1)
@assert(seq[i + 1] == seq_copy[i + 1])
end
@assert(seq[1] == 1)
@assert(seq[3] == 3)
@assert(seq[end] == 5)
x = 1
@assert(seq[x + 1] == 2)
end

main()
