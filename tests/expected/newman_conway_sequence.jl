#=  Python program to find the n-th element of
    Newman-Conway Sequence =#
function newman_conway_sequence(n::Int64)::Int64
    r = 0
    f = [0, 1, 1]
    for i = 3:n
        r = f[f[i]+1] + f[i-f[i]+1]
        push!(f, r)
    end
    return r
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(newman_conway_sequence(10) == 6)
    @assert(newman_conway_sequence(30) == 16)
    @assert(newman_conway_sequence(1000) == 510)
end
