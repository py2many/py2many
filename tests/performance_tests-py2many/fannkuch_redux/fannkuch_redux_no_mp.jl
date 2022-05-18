using ResumableFunctions

@resumable function permutations(n, start, size)
    p = Vector{UInt8}(0:n-1)
    count = Vector{UInt8}(n)
    remainder = start
    for v = -1:-1:n-1
        count[v+1], remainder = div(remainder)
        for _ = 0:count[v+1]-1
            p[begin:v], p[v+1] = (p[2:v+1], p[1])
        end
    end
    @assert(count[2] == 0)
    @assert(size < 2 || (size % 2) == 0)
    if size < 2
        @yield p[begin:end]
    else
        rotation_swaps = [nothing] * n
        for i = 1:n-1
            r = collect(0:n-1)
            for v = 1:i
                r[begin:v], r[v+1] = (r[2:v+1], r[1])
            end
            swaps = []
            for (dst, src) in enumerate(r)
                if dst != src
                    push!(swaps, (dst, src))
                end
            end
            rotation_swaps[i+1] = tuple(swaps)
        end
        while true
            @yield p[begin:end]
            p[1], p[2] = (p[2], p[1])
            @yield p[begin:end]
            i = 2
            while count[i+1] >= i
                count[i+1] = 0
                i += 1
            end
        end
    end
end

@resumable function alternating_flips_generator(n, start, size)
    maximum_flips = 0
    alternating_factor = 1
    for permutation in (permutations(n, start, size) for _ in (0:size))
        first = permutation[1]
        if first
            flips_count = 1
            while true
                permutation[begin:first+1] = permutation[end:-1:first+1]
                first = permutation[1]
                if !(first)
                    has_break = true
                    break
                end
                flips_count += 1
            end
            if maximum_flips < flips_count
                maximum_flips = flips_count
            end
            @yield flips_count * alternating_factor
        else
            @yield 0
        end
        alternating_factor = -(alternating_factor)
    end
    @yield maximum_flips
end

function task(n, start, size)::Tuple
    alternating_flips = alternating_flips_generator(n, start, size)
    return (sum((alternating_flips for _ in (0:size))), alternating_flips)
end

function fannkuch(n)
    if n < 0
        for data in (permutations(-(n), 0, factorial(-(n))) for _ in (0:factorial(-(n))))
            println(join(map((n) -> string(n + 1), data), ""))
        end
    else
        @assert(n > 0)
        task_size = factorial(n)
        checksums, maximums = zip(task(n, 0, task_size))
        checksum, maximum = (sum(checksums), max(maximums))
        println("$(checksum)\nPfannkuchen($(n)) = $(maximum)")
    end
end

function main()
    fannkuch(10)
end

main()
