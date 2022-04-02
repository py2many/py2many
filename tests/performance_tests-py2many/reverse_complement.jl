using ResumableFunctions


reverse_translation = Dict(
    b"A" => b"T",
    b"B" => b"V",
    b"C" => b"G",
    b"D" => b"H",
    b"G" => b"C",
    b"H" => b"D",
    b"K" => b"M",
    b"M" => b"K",
    b"N" => b"N",
    b"R" => b"Y",
    b"S" => b"S",
    b"T" => b"A",
    b"U" => b"A",
    b"V" => b"B",
    b"W" => b"W",
    b"Y" => b"R",
    b"a" => b"T",
    b"b" => b"V",
    b"c" => b"G",
    b"d" => b"H",
    b"g" => b"C",
    b"h" => b"D",
    b"k" => b"M",
    b"m" => b"K",
    b"n" => b"N",
    b"r" => b"Y",
    b"s" => b"S",
    b"t" => b"A",
    b"u" => b"A",
    b"v" => b"B",
    b"w" => b"W",
    b"y" => b"R",
)
function reverse_complement(header, sequence)::Tuple
    t = replace!(reverse_translation, b"\n\r ")
    output = Vector{UInt8}()
    trailing_length = length(t) % 60
    if trailing_length
        output += b"\n" + t[begin:trailing_length]
    end
    for i in (trailing_length:60:length(t)-1)
        output += b"\n" + t[(i+1):i+60]
    end
    return (header, output[begin:end])
end

@resumable function read_sequences(file)
    for line in file
        if line[1] == ord(">")
            header = line
            sequence = Vector{UInt8}()
            for line in file
                if line[1] == ord(">")
                    @yield (header, sequence)
                    header = line
                    sequence = Vector{UInt8}()
                else
                    sequence += line
                end
            end
            @yield (header, sequence)
            break
        end
    end
end

@resumable function merge(v, g)
    @yield v
    for w in g
        @yield w
    end
end

function main()
    write_ = x -> write(stdout, x)
    flush_ = flush(stdout)
    s = read_sequences(stdin.buffer)
    data = next(s)
    for (h, r) in starmap(reverse_complement, merge(data, s))
        write_(h)
        write_(r)
    end
end

main()
