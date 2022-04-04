function generator1()
    Channel() do ch_generator1
        for i in (0:2)
            put!(ch_generator1, i)
        end
    end
end

function generator2()
    Channel() do ch_generator2
        for j in (3:4)
            put!(ch_generator2, j)
        end
    end
end

function yield_from()
    # Unsupported
    @yield_from generator1()
    # Unsupported
    @yield_from generator2()
end

function main()
    arr = []
    for i in yield_from()
        push!(arr, i)
    end
    @assert(arr == [0, 1, 2, 3, 4])
end

main()
