using BenchmarkTools

function column_major(array::Vector{Int})
    inds = axes(array, 1)
    new_array = similar(Array{Int}, inds, inds)
    for i = inds
        new_array[:, i] = array
    end
    return new_array
end

function row_major(array::Vector{Int})
    inds = axes(array, 1)
    new_array = similar(Array{Int}, inds, inds)
    for i = inds
        new_array[i, :] = array
    end
    return new_array
end

function run_benchmarks()
    arr = zeros(Int, 20000)
    println("Finished populating array")

    # Benchmarking
    @time column_major(arr) # ~ 1 sec
    @time row_major(arr) # ~ 7 sec
    println("Finished Tests")
end

run_benchmarks()