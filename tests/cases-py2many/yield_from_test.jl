using ResumableFunctions
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

@resumable function yield_from()
    for v in generator1()
        @yield v
    end
    for v in generator2()
        @yield v
    end
end

function main()
    arr = []
    for i in yield_from()
        push!(arr, i)
    end
    @assert(arr == [0, 1, 2, 3, 4])
end

main()
