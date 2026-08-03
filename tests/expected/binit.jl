
function bisect_right(data::Array{Int64}, item::Int64)::Int64
    low = 0
    high::Int64 = Int64(length(data))
    while low < high
        middle = Int64(floor((low + high) / 2))
        if item < data[middle+1]
            high = middle
        else

            low = middle + 1
        end
    end
    return low
end

function bin_it(limits::Array{Int64}, data::Array{Int64})::Array{Int64}
    bins = [0]
    for _x in limits
        push!(bins, 0)
    end
    for d in data
        bins[bisect_right(limits, d)+1] += 1
    end
    return bins
end

function main()
    limits = [23, 37, 43, 53, 67, 83]
    data = [
        95,
        21,
        94,
        12,
        99,
        4,
        70,
        75,
        83,
        93,
        52,
        80,
        57,
        5,
        53,
        86,
        65,
        17,
        92,
        83,
        71,
        61,
        54,
        58,
        47,
        16,
        8,
        9,
        32,
        84,
        7,
        87,
        46,
        19,
        30,
        37,
        96,
        6,
        98,
        40,
        79,
        97,
        45,
        64,
        60,
        29,
        49,
        36,
        43,
        55,
    ]
    @assert(bin_it(limits, data) == [11, 4, 2, 6, 9, 5, 13])
    println(join(["OK"], " "))
end

main()
