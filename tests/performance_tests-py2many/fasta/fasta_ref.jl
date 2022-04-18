#=
The Computer Language Benchmarks Game
https://salsa.debian.org/benchmarksgame-team/benchmarksgame/

Contributed by Adam Beckmeyer. Based on Drake Diedrich's C implementation #9
=#

const LINESIZE = 60
const BUFFERLINES = 1000

const IM = 139968 % Int32
const IA = 3877 % Int32
const IC = 29573 % Int32
const SEED = Ref(42 % UInt32)

function gen_random()
    SEED[] = ((SEED[] * IA) + IC) % IM
end

# Vector{UInt8} faster indexing than Base.CodeUnits{UInt8,String} (julia 1.2)
const alu = Vector{UInt8}(
    string(
        "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG",
        "GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA",
        "CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT",
        "ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA",
        "GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG",
        "AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC",
        "AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA",
    ),
)

const iub = "acgtBDHKMNRSVWY"
const iub_prob = [
    0.27,
    0.12,
    0.12,
    0.27,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
    0.02,
]
const homosapiens = "acgt"
const homosapiens_prob =
    [0.3029549426680, 0.1979883004921, 0.1975473066391, 0.3015094502008]

# Build a lookup table such that table[i+1] gives the appropriate UInt8 from chars
function lookup_table(chars, probs)
    table = Vector{UInt8}(undef, IM)
    cumprob = probs[1]
    probi = 1
    @inbounds for i = 0:IM-1
        if i / IM >= cumprob
            probi += 1
            cumprob += probs[probi]
        end
        @inbounds table[i+1] = chars[probi] % UInt8
    end
    return table
end

function repeat_fasta(io, src, n)
    # First create a buffer that repeats the src enough times that the beginning of src
    # aligns with a new line again
    buf_lines = length(src)
    buf = fill('\n' % UInt8, buf_lines * (LINESIZE + 1))

    iter = Iterators.Stateful(Iterators.cycle(src))
    for l = 0:buf_lines-1, i = 1:LINESIZE
        @inbounds buf[l*(LINESIZE+1)+i] = popfirst!(iter)
    end

    # Then write that whole buffer out as many times as you can fit within n
    buffer_count = n ÷ LINESIZE ÷ buf_lines
    for _ = 1:buffer_count
        write(io, buf)
    end

    # And partially write it to make up the rest of n
    remaining_full_lines = n ÷ LINESIZE - buffer_count * buf_lines
    partial_line_chars =
        n - buffer_count * buf_lines * LINESIZE - remaining_full_lines * LINESIZE

    resize!(buf, remaining_full_lines * (LINESIZE + 1) + partial_line_chars)
    write(io, buf)
    partial_line_chars == 0 || write(io, '\n')
end

function random_fasta(io, table, n)
    # Create a buffer to be filled with lines of random fasta output
    buf = fill('\n' % UInt8, BUFFERLINES * (LINESIZE + 1))

    # Fill the whole buffer for most of the data skipping over linebreaks
    buffer_count = n ÷ LINESIZE ÷ BUFFERLINES
    for _ = 1:buffer_count
        for l = 0:BUFFERLINES-1, i = 1:LINESIZE
            @inbounds buf[l*(LINESIZE+1)+i] = table[gen_random()+1]
        end
        write(io, buf)
    end

    # Handle remaining lines
    remaining_full_lines = n ÷ LINESIZE - buffer_count * BUFFERLINES
    for l = 0:remaining_full_lines-1, i = 1:LINESIZE
        @inbounds buf[l*(LINESIZE+1)+i] = table[gen_random()+1]
    end

    # Handle remaining partial line
    partial_line_chars =
        n - buffer_count * BUFFERLINES * LINESIZE - remaining_full_lines * LINESIZE
    for i = 1:partial_line_chars
        @inbounds buf[remaining_full_lines*(LINESIZE+1)+i] = table[gen_random()+1]
    end

    # Write out remaining lines and partial line
    resize!(buf, remaining_full_lines * (LINESIZE + 1) + partial_line_chars)
    write(io, buf)

    # If there was no partial line, the output already has a newline at end; otherwise write one
    partial_line_chars == 0 || write(io, '\n')
end

function fasta(n, io = stdout)
    write(io, ">ONE Homo sapiens alu\n")
    repeat_fasta(io, alu, 2n)

    write(io, ">TWO IUB ambiguity codes\n")
    random_fasta(io, lookup_table(iub, iub_prob), 3n)
    write(io, ">THREE Homo sapiens frequency\n")
    random_fasta(io, lookup_table(homosapiens, homosapiens_prob), 5n)
end

isinteractive() || @time fasta(1000000)
# fasta(parse(Int,ARGS[1]))
