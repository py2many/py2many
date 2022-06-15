#=  Python program to find the n-th element of
    Newman-Conway Sequence =#
function sequence(n::Int64)
    f = [0, 1, 1]
    for i = 3:n
        r = f[f[i]+1] + f[i-f[i]+1]
        push!(f, r)
    end
    return r
end

if abspath(PROGRAM_FILE) == @__FILE__
    n = 10
    println(sequence(n))
end
