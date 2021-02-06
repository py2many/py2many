
function bisect_right(data::Array{Int64}, item::Int64)::Int64
    low = 0
    high = length(data)
    while low < high
        middle = i32::from(((low + high) / 2))
        if item < data[middle]
            high = middle
        else

            low = (middle + 1)
        end
    end
    return low
end

function bin_it(limits::Array{Int64}, data::Array{Int64})::Array{Int64}
    bins = [0]
    for x in limits
        bins.push(0)
    end
    for d in data
        bins[bisect_right(limits, d)] += 1
    end
    return bins
end
