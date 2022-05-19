using Distributed
using StringEncodings

abstract type Abstractlean_call end
lean_buffer = Dict()
function lean_args(sequence, reading_frames, i, j)
    global lean_buffer
    lean_key = length(lean_buffer)
    lean_buffer[lean_key] = sequence
    return (lean_key, reading_frames, i, j)
end

mutable struct lean_call <: Abstractlean_call
    func
end
function __call__(self::lean_call, lean_key, reading_frames, i, j)::Vector
    global lean_buffer
    sequence = lean_buffer[lean_key]
    results = func(self, sequence, reading_frames, i, j)
    lean_results = []
    for (frame, n, frequences) in results
        lean_frequences = defaultdict(int)
        for (reading_frame, bits_list) in reading_frames
            if reading_frame == frame
                for bits in bits_list
                    lean_frequences[bits+1] = frequences[bits+1]
                end
            end
        end
        push!(lean_results, (frame, n, lean_frequences))
    end
    return lean_results
end

function count_frequencies(sequence, reading_frames, i, j)
    frames = tuple(sorted([frame for (frame, _) in reading_frames], true))
    frequences_mask_list =
        tuple(((defaultdict(int), (1 << repeat([frame...], 2)) - 1) for frame in frames)...)
    frame = frames[1]
    frequences, mask = frequences_mask_list[1]
    short_frame_frequences = frequences_mask_list[2:end]
    mono_nucleotides = []
    frame_tail = length(frames) - 1
    if frame_tail >= 0 && frames[frame_tail+1] == 1
        freq = frequences_mask_list[frame_tail+1][1]
        worklist = sequence[i+1:j]
        len_before = length(worklist)
        while len_before > 0
            n = worklist[1:1]
            worklist = translate(worklist, nothing, n)
            len_after = length(worklist)
            freq[n[1]+1] = len_before - len_after
            len_before = len_after
            push!(mono_nucleotides, n)
        end
        frame_tail -= 1
    end
    if frame_tail >= 0 && frames[frame_tail+1] == 2 && mono_nucleotides
        freq = frequences_mask_list[frame_tail+1][1]
        worklist = sequence[i+1:min(j + 1, length(sequence))]
        overlaps = []
        for v in (n + m for n in mono_nucleotides for m in mono_nucleotides)
            bits = append!(repeat(v[1], 4), v[2])
            freq[bits+1] = count(worklist, v)
            if v[2:end] == v[begin:1]
                push!(overlaps, (v, bits, append!(v[begin:1], v)))
            end
        end
        for (v, bits, pattern) in overlaps
            count = length(worklist)
            tmp = replace(worklist, pattern + pattern, b"12")
            tmp = replace(tmp, pattern, b"1")
            count = (count - length(tmp)) ÷ 2
            count += count(tmp, b"1" + v)
            count += count(tmp, b"2" + v[begin:1])
            freq[bits+1] += count
        end
        frame_tail -= 1
    end
    short_frame_frequences = short_frame_frequences[begin:frame_tail]
    if length(short_frame_frequences) != 0
        bits = 0
        if i == 0
            for k = i:(i+frame)-2
                bits = bits * 4 + sequence[k+1]
                for (t, (f, m)) in enumerate(short_frame_frequences)
                    if ((k - i) + 1) >= frames[t+1]
                        f[bits&m+1] += 1
                    end
                end
            end
        else
            for k = (i-frame)+1:i-1
                bits = bits * 4 + sequence[k+1]
            end
        end
        for byte in sequence[k+2:j]
            bits = (bits * 4 + byte) & mask
            frequences[bits+1] += 1
            for (f, m) in short_frame_frequences
                f[bits&m+1] += 1
            end
        end
    end
    return [
        (frame, (length(sequence) - frame) + 1, frequences_mask_list[i+1][1]) for
        (i, frame) in enumerate(frames)
    ]
end

function read_sequence(file, header, translation)::Vector{Int8}
    for line in file
        if line[1] == Int(codepoint('>'))
            if line[2:length(header)+1] == header
                has_break = true
                break
            end
        end
    end
    sequence = Vector{UInt8}()
    for line in file
        if line[1] == Int(codepoint('>'))
            has_break = true
            break
        end
        sequence += line
    end
    return replace!(
        collect(sequence),
        merge!(translation, Dict(b"\n" => b"", b"\r" => b"", b"\t" => b"", b" " => b""))...,
    )
end

function lookup_frequency(results, frame, bits)
    n = 1
    frequency = 0
    for (_, n, frequencies) in filter((r) -> r[1] == frame, results)
        frequency += frequencies[bits+1]
    end
    return (frequency, n > 0 ? (n) : (1))
end

function display(results, display_list, sort = false, relative = false, end_ = "\n")
    lines = [
        (k_nucleotide, lookup_frequency(results, frame, bits)) for
        (k_nucleotide, frame, bits) in display_list
    ]
    if sort
        lines = sorted(lines, (v) -> (-(v[2][1]), v[1]))
    end
    for (k_nucleotide, (frequency, n)) in lines
        if relative
            println("$(k_nucleotide) $(frequency*100.0 / n:.3f)")
        else
            println("$(frequency)\t$(k_nucleotide)")
        end
    end
    println(end_)
end

function main()
    translation = Dict(
        b"G" => b"\x00",
        b"T" => b"\x01",
        b"C" => b"\x02",
        b"A" => b"\x03",
        b"g" => b"\x00",
        b"t" => b"\x01",
        b"c" => b"\x02",
        b"a" => b"\x03",
    )
    function str_to_bits(text)::Int64
        buffer = translate(encode(text, "latin1"), translation)
        bits = 0
        for k = 0:length(buffer)-1
            bits = bits * 4 + buffer[k+1]
        end
        return bits
    end

    function display_list(k_nucleotides)
        return [(n, length(n), str_to_bits(n)) for n in k_nucleotides]
    end

    sequence = read_sequence(stdin.buffer, b"THREE", translation)
    mono_nucleotides = ("G", "A", "T", "C")
    di_nucleotides = tuple((n * m for n in mono_nucleotides for m in mono_nucleotides)...)
    k_nucleotides = ("GGT", "GGTA", "GGTATT", "GGTATTTTAATT", "GGTATTTTAATTTATAGT")
    reading_frames = append!(
        [
            (1, tuple(map(str_to_bits, mono_nucleotides))),
            (2, tuple(map(str_to_bits, di_nucleotides))),
        ],
        collect(map((s) -> (length(s), (str_to_bits(s),)), k_nucleotides)),
    )
    if length(sequence) > (128 * length(Sys.cpu_info()))
        n = length(Sys.cpu_info())
    else
        n = 1
    end
    partitions = [length(sequence) * i ÷ n for i = 0:n]
    count_jobs = [
        (sequence, reading_frames, partitions[i+1], partitions[i+2]) for
        i = 0:length(partitions)-2
    ]
    if n == 1
        results = collect(chain(starmap(count_frequencies, count_jobs)...))
    else
        lean_jobs = collect(starmap(lean_args, count_jobs))
        default_worker_pool() do pool
            async_results = starmap_async(pool, lean_call(count_frequencies), lean_jobs)
            results = collect(chain(get(async_results)...))
        end
    end
    display(results, display_list(mono_nucleotides))
    display(results, display_list(di_nucleotides))
    display(results, display_list(k_nucleotides))
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
