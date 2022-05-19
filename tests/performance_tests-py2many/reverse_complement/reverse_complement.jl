
COMPLEMENTS = Dict(
    b"A" => b"T",
    b"C" => b"G",
    b"G" => b"C",
    b"T" => b"A",
    b"U" => b"A",
    b"M" => b"K",
    b"R" => b"Y",
    b"W" => b"W",
    b"S" => b"S",
    b"Y" => b"R",
    b"K" => b"M",
    b"V" => b"B",
    b"H" => b"D",
    b"D" => b"H",
    b"B" => b"V",
    b"N" => b"N",
    b"a" => b"T",
    b"c" => b"G",
    b"g" => b"C",
    b"t" => b"A",
    b"u" => b"A",
    b"m" => b"K",
    b"r" => b"Y",
    b"w" => b"W",
    b"s" => b"S",
    b"y" => b"R",
    b"k" => b"M",
    b"v" => b"B",
    b"h" => b"D",
    b"d" => b"H",
    b"b" => b"V",
    b"n" => b"N",
)
COMMENT = Int(codepoint('>'))
function reverse_sequence(sequence)::Vector{Int8}
    chunk = Vector{UInt8}()
    complemented = translate(sequence, COMPLEMENTS, b"\n")
    seq_len = length(complemented)
    last_line_len = seq_len % 60
    if last_line_len != 0
        chunk += b"\n" + complemented[begin:last_line_len]
    end
    for i = last_line_len:60:seq_len-1
        chunk += b"\n" + complemented[i+1:i+60]
    end
    return chunk[end:-1:begin]
end

function generate_sequences(lines)
    Channel() do ch_generate_sequences
        heading = nothing
        sequence = Vector{UInt8}()
        for line in lines
            if line[1] == COMMENT
                if heading
                    put!(ch_generate_sequences, (heading, sequence))
                    sequence = Vector{UInt8}()
                end
                heading = line
            else
                sequence += line
            end
        end
        put!(ch_generate_sequences, (heading, sequence))
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    stdin = readline(0)
    for (heading, sequence) in generate_sequences(stdin.buffer)
        write(stdout, heading)
        write(stdout, reverse_sequence(sequence))
        flush(stdout)
    end
end
