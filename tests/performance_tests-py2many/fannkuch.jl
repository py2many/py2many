using ResumableFunctions


using multiprocessing: cpu_count, Pool
using itertools: islice, starmap
@resumable function permutations(n, start, size)
    p = Vector{UInt8}(join((0:n-1), ""))
    count = Vector{UInt8}(join(n, ""))
    remainder = start
    for v in (n-1:-1:-1)
        count[v+1], remainder = divmod(remainder, factorial(v))
        for _ in (0:count[v+1]-1)
            p[begin:v], p[v+1] = (p[2:v+1], p[1])
        end
    end
    @assert(count[2] == 0)
    @assert(size < 2 || (size % 2) == 0)
    if size < 2
        @yield p[begin:end]
    else
        rotation_swaps = [nothing] * n
        for i in (1:n-1)
            r = collect((0:n-1))
            for v in (1:i+1-1)
                r[begin:v], r[v+1] = (r[2:v+1], r[1])
            end
            swaps = []
            for (dst, src) in r.iter().enumerate()
                if dst != src
                    push!(swaps, (dst, src))
                end
            end
            rotation_swaps[i] = tuple(swaps)
        end
        while true
            @yield p[begin:end]
            p[1], p[2] = (p[2], p[1])
            @yield p[begin:end]
            i = 2
            while count[i] >= i
                count[i] = 0
                i += 1
            end
        end
    end
end

@resumable function alternating_flips_generator(n, start, size)
    maximum_flips = 0
    alternating_factor = 1
    for permutation in split(permutations(n, start, size))[size]
        first = permutation[1]
        if first
            flips_count = 1
            while true
                permutation[begin:first+1] = permutation[(first+1):end]
                first = permutation[1]
                if !(first)
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

function task(n, start, size)
    alternating_flips = alternating_flips_generator(n, start, size)
    return (sum(split(alternating_flips)[size]), next(alternating_flips))
end

function fannkuch(n)
    if n < 0
        for data in split(permutations(-(n), 0, factorial(-(n))))[factorial(-(n))]
            println(join("", map((n) -> string(n + 1), data)))
        end
    else
        @assert(n > 0)
        task_count = length(Sys.cpu_info())
        total = factorial(n)
        task_size = ((total + task_count) - 1) / task_count
        if task_size < 20000
            task_size = total
            task_count = 1
        end
        @assert((task_size % 2) == 0)
        task_args = [(n, i * task_size, task_size) for i in (0:task_count-1)]
        if task_count > 1
            Pool() do pool
                checksums, maximums = zip(starmap(pool, task, task_args)...)
            end
        else
            checksums, maximums = zip(starmap(task, task_args)...)
        end
        checksum, maximum = (sum(checksums), max(maximums))
        println(format("{0}\nPfannkuchen({1}) = {2}", checksum, n, maximum))
    end
end

function main()
    arg::Int64 = 12
    fannkuch(arg)
end

main()
