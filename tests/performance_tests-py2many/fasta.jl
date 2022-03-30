using ResumableFunctions
using BisectPy: bisect
using contextlib: closing, contextmanager
using itertools: accumulate, chain, islice, zip_longest
using multiprocessing: Lock, RawValue, Process

using re: sub

write = write(stdout.buffer)
function acquired_lock()
    lock = Lock()
    acquire(lock)
    return lock
end

function started_process(target, args)
    process = Process(target, args)
    start(process)
    return process
end

@resumable function lock_pair(pre_lock = nothing, post_lock = nothing, locks = nothing)
    pre, post = locks ? (locks) : ((pre_lock, post_lock))
    if pre
        acquire(pre)
    end
    @yield
    if post
        release(post)
    end
end

function write_lines(
    sequence,
    n,
    width,
    lines_per_block = 10000,
    newline = b"\n",
    table = nothing,
)
    i = 0
    blocks = ((n - width) ÷ width) ÷ lines_per_block
    if blocks
        for _ in (0:blocks-1)
            output = Vector{UInt8}()
            for i in (i:width:i+width*lines_per_block-1)
                output += sequence[(i+1):i+width] + newline
            end
            if table
                write(translate(output, table))
            else
                write(output)
            end
        end
    end
    output = Vector{UInt8}()
    if i < (n - width)
        for i in (i:width:n-width-1)
            output += sequence[(i+1):i+width] + newline
        end
    end
    output += sequence[(i+1):n] + newline
    if table
        write(translate(output, table))
    else
        write(output)
    end
    flush(stdout.buffer)
end

function cumulative_probabilities(alphabet, factor = 1.0)
    probabilities = tuple(accumulate((p * factor for (_, p) in alphabet)))
    table = maketrans(
        bytearray,
        bytes(chain((0:length(alphabet)-1), [255])),
        bytes(chain((ord(c) for (c, _) in alphabet), [10])),
    )
    return (probabilities, table)
end

function copy_from_sequence(header, sequence, n, width, locks = nothing)
    sequence = Vector{UInt8}(join(sequence, ""))
    while length(sequence) < n
        extend(sequence, sequence)
    end
    lock_pair() do
        write(header)
        write_lines(sequence, n, width)
    end
end

@resumable function lcg(seed, im, ia, ic)
    local_seed = value(seed)
    try
        while true
            local_seed = (local_seed * ia + ic) % im
            @yield local_seed
        end
    finally
        value(seed) = local_seed
    end
end

@resumable function lookup(probabilities, values)
    for value in values
        @yield bisect(probabilities, value)
    end
end

function lcg_lookup_slow(probabilities, seed, im, ia, ic)
    closing(lcg(seed, im, ia, ic)) do prng
        @yield from lookup(probabilities, prng)
    end
end

@resumable function lcg_lookup_fast(probabilities, seed, im, ia, ic)
    local_seed = value(seed)
    try
        while true
            local_seed = (local_seed * ia + ic) % im
            @yield bisect(probabilities, local_seed)
        end
    finally
        value(seed) = local_seed
    end
end

function lookup_and_write(
    header,
    probabilities,
    table,
    values,
    start,
    stop,
    width,
    locks = nothing,
)
    if isa(values, bytearray)
        output = values
    else
        output = Vector{UInt8}()
        output[begin:stop-start] = lookup(probabilities, values)
    end
    lock_pair() do
        if start == 0
            write(header)
        end
        write_lines(output, length(output), width)
    end
end

function random_selection(header, alphabet, n, width, seed, locks = nothing)
    im = 139968.0
    ia = 3877.0
    ic = 29573.0
    probabilities, table = cumulative_probabilities(alphabet, im)
    if !(locks)
        closing(lcg_lookup_fast(probabilities, seed, im, ia, ic)) do prng
            output = Vector{UInt8}(join(split(prng)[n], ""))
        end
        lookup_and_write(header, probabilities, table, output, 0, n, width)
    else
        pre_seed, post_seed, pre_write, post_write = locks
        m = n > (width * 15) ? (length(Sys.cpu_info()) * 3) : (1)
        partitions = [(n ÷ width * m) * width * i for i in (1:m-1)]
        processes = []
        pre = pre_write
        lock_pair() do
            closing(lcg(seed, im, ia, ic)) do prng
                for (start, stop) in zip([0] + partitions, partitions + [n])
                    values = collect(split(prng)[stop-start])
                    post = stop < n ? (acquired_lock()) : (post_write)
                    push!(
                        processes,
                        started_process(
                            lookup_and_write,
                            (
                                header,
                                probabilities,
                                table,
                                values,
                                start,
                                stop,
                                width,
                                (pre, post),
                            ),
                        ),
                    )
                    pre = post
                end
            end
        end
        for p in processes
            join(p)
        end
    end
end

function fasta(n)
    alu = sub(
        "\s+",
        "",
        "\nGGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGA\nTCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACT\nAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAG\nGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCG\nCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA\n",
    )
    iub = collect(zip_longest("acgtBDHKMNRSVWY", (0.27, 0.12, 0.12, 0.27), 0.02))
    homosapiens = collect(
        zip("acgt", (0.302954942668, 0.1979883004921, 0.1975473066391, 0.3015094502008)),
    )
    seed = RawValue("f", 42)
    width = 60
    tasks = [
        (copy_from_sequence, [b">ONE Homo sapiens alu\n", alu, n * 2, width]),
        (random_selection, [b">TWO IUB ambiguity codes\n", iub, n * 3, width, seed]),
        (
            random_selection,
            [b">THREE Homo sapiens frequency\n", homosapiens, n * 5, width, seed],
        ),
    ]
    if length(Sys.cpu_info()) < 2
        for (func, args) in tasks
            func(args...)
        end
    else
        written_1 = acquired_lock()
        seeded_2 = acquired_lock()
        written_2 = acquired_lock()
        locks_sets = [
            (nothing, written_1),
            (nothing, seeded_2, written_1, written_2),
            (seeded_2, nothing, written_2, nothing),
        ]
        processes = [
            started_process(target, args + [locks_sets[i]]) for
            (i, (target, args)) in tasks.iter().enumerate()
        ]
        for p in processes
            join(p)
        end
    end
end

function main()
    fasta(parse(Int, argv[2]))
end

main()
