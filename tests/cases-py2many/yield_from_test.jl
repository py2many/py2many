using ResumableFunctions
@resumable function generator1()
    for i in (0:2)
        @yield i
    end
end

@resumable function generator2()
    for j in (3:4)
        @yield j
    end
end

function yield_from()
    generator1()
    generator2()
end

function main()
    arr = []
    for i in yield_from()
        push!(arr, i)
    end
    @assert(arr == [0, 1, 2, 3, 4])
end

main()
