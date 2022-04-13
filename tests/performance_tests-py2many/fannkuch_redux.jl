using Distributed




function permutations(n, start, size)
    Channel() do ch_permutations
        p = Vector{UInt8}((0:n-1))
        count = Vector{UInt8}(n)
        remainder = start
        for v in (n-1:-1:-1)
            count[v], remainder = div(remainder)
            for _ in (0:count[v]-1)
                p[begin:v], p[v] = (p[2:v+1], p[0])
            end
        end
        @assert(count[1] == 0)
        @assert(size < 2 || (size % 2) == 0)
        if size < 2
            put!(ch_permutations, p[begin:end])
        else
            rotation_swaps = [nothing] * n
            for i in (1:n-1)
                r = collect((0:n-1))
                for v in (1:i+1-1)
                    r[begin:v], r[v] = (r[2:v+1], r[0])
                end
                swaps = []
                for (dst, src) in enumerate(r)
                    if dst != src
                        append(swaps, (dst, src))
                    end
                end
                rotation_swaps[i] = tuple(swaps)
            end
            while true
                put!(ch_permutations, p[begin:end])
                p[0], p[1] = (p[1], p[0])
                put!(ch_permutations, p[begin:end])
                i = 2
                while count[i] >= i
                    count[i] = 0
                    i += 1
                end
            end
        end
    end
end

function alternating_flips_generator(n, start, size)
    Channel() do ch_alternating_flips_generator
        maximum_flips = 0
        alternating_factor = 1
        for permutation in (permutations(n, start, size) for _ in (0:size))
            first = permutation[0]
            if first
                flips_count = 1
                while true
                    permutation[begin:first+1] = permutation[(first+1):end]
                    first = permutation[0]
                    if !(first)
                        break
                    end
                    flips_count += 1
                end
                if maximum_flips < flips_count
                    maximum_flips = flips_count
                end
                put!(ch_alternating_flips_generator, flips_count * alternating_factor)
            else
                put!(ch_alternating_flips_generator, 0)
            end
            alternating_factor = -(alternating_factor)
        end
        put!(ch_alternating_flips_generator, maximum_flips)
    end
end

function task(n, start, size)::Tuple
    alternating_flips = alternating_flips_generator(n, start, size)
    return (sum((alternating_flips for _ in (0:size))), take!(alternating_flips))
end

function fannkuch(n)
    if n < 0
        for data in (permutations(-(n), 0, factorial(-(n))) for _ in (0:factorial(-(n))))
            println(join(map((n) -> string(n + 1), data), ""))
        end
    else
        @assert(n > 0)
        task_count = length(Sys.cpu_info())
        total = factorial(n)
        task_size = ((total + task_count) - 1) ÷ task_count
        if task_size < 20000
            task_size = total
            task_count = 1
        end
        @assert((task_size % 2) == 0)
        task_args = [(n, i * task_size, task_size) for i in (0:task_count-1)]
        if task_count > 1
            default_worker_pool() do pool
                checksums, maximums = zip(pmap(task, task_args)...)
            end
        else
            checksums, maximums = zip(starmap(task, task_args)...)
        end
        checksum, maximum = (sum(checksums), max(maximums))
        println("$checksum\nPfannkuchen($n) = $maximum")
    end
end

function main()
    fannkuch(parse(Int, argv[1]))
end

main()
