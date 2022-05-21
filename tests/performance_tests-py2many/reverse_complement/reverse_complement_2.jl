using Distributed
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
function reverse_complement(header, sequence)
    t = translate(sequence, reverse_translation, b"\n\r ")
    output = Vector{UInt8}()
    trailing_length = length(t) % 60
    if trailing_length != 0
        output += b"\n" + t[begin:trailing_length]
    end
    for i = trailing_length:60:length(t)-1
        output += b"\n" + t[i+1:i+60]
    end
    return (header, output[end:-1:begin])
end

function read_sequences(file)
    Channel() do ch_read_sequences
        Channel() do ch_read_sequences
            for line in file
                if line[1] == Int(codepoint('>'))
                    header = line
                    sequence = Vector{UInt8}()
                    for line in file
                        if line[1] == Int(codepoint('>'))
                            put!(ch_read_sequences, (header, sequence))
                            header = line
                            sequence = Vector{UInt8}()
                        else
                            sequence += line
                        end
                    end
                    put!(ch_read_sequences, (header, sequence))
                    has_break = true
                    break
                end
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    write = x -> Base.write(stdout, x)
    flush = Base.flush(stdout)
    s = read_sequences(stdin.buffer)
    data = take!(s)
    @resumable function merge(v, g)
        @yield v
        for w in g
            @yield w
        end
    end

    for (h, r) in starmap(reverse_complement, merge(data, s))
        write(h)
        write(r)
        flush
    end
end
