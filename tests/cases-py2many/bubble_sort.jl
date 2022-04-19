
function bubble_sort(seq::Vector{Int64})::Vector{Int64}
    L = length(seq)
    for _ = 1:L
        for n = 2:L
            if seq[n] < seq[n-1]
                seq[n-1], seq[n] = (seq[n], seq[n-1])
            end
        end
    end
    return seq
end

function main()
    unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    @assert(bubble_sort(unsorted) == expected)
    println("OK")
end

main()
