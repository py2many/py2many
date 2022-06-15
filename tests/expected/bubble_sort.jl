
function bubble_sort(seq::Vector{Int64})::Vector{Int64}
    l = length(seq)
    for _ = 0:l-1
        for n = 1:l-1
            if seq[n+1] < seq[n]
                (seq[n], seq[n+1]) = (seq[n+1], seq[n])
            end
        end
    end
    return seq
end

if abspath(PROGRAM_FILE) == @__FILE__
    unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    @assert(bubble_sort(unsorted) == expected)
    println("OK")
end
