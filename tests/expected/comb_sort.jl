
function comb_sort(seq::Vector{Int64})::Vector{Int64}
    gap = length(seq)
    swap = true
    while gap > 1 || swap
        gap = max(1, floor(Int, gap / 1.25))
        swap = false
        for i = 0:length(seq)-gap-1
            if seq[i+1] > seq[i+gap+1]
                (seq[i+1], seq[i+gap+1]) = (seq[i+gap+1], seq[i+1])
                swap = true
            end
        end
    end
    return seq
end

if abspath(PROGRAM_FILE) == @__FILE__
    unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    @assert(comb_sort(unsorted) == expected)
    println("OK")
end
