using BisectPy
using ResumableFunctions
# using Continuables

alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"
iub = collect(
    zip(
        ["a", "c", "g", "t", "B", "D", "H", "K", "M", "N", "R", "S", "V", "W", "Y"],
        append!([0.27, 0.12, 0.12, 0.27], repeat([0.02], 11)),
    ),
)
homosapiens = [
    ("a", 0.302954942668),
    ("c", 0.1979883004921),
    ("g", 0.1975473066391),
    ("t", 0.3015094502008),
]
# genRandom(ia::Int64 = 3877, ic::Int64 = 29573, im::Int64 = 139968) = @cont begin 
#     seed = 42
#     imf = float(im)
#     while true
#         seed = (seed * ia + ic) % im
#         cont(seed / imf)
#     end
# end
@resumable function genRandom(
    ia::Int64 = 3877,
    ic::Int64 = 29573,
    im::Int64 = 139968,
)::Float64
    seed = 42
    imf = float(im)
    while true
        seed = (seed * ia + ic) % im
        @yield seed / imf
    end
end

Random = genRandom()
function makeCumulative(
    table::Vector{Tuple{String,Float64}},
)::Tuple{Vector{Float64},Vector{String}}
    P::Vector{Float64} = []
    C::Vector{String} = []
    prob = 0.0
    for (char, p) in table
        prob += p
        P = append!(P, [prob])
        C = append!(C, [char])
    end
    return (P, C)
end

function repeatFasta(src::String, n::Int64)
    width = 60
    r = length(src)
    s = src * src * src[begin:n%r]
    for j in (0:n÷width-1)
        i = j * width % r
        println(s[(i+1):i+width])
    end
    if (n % width) != 0
        println(s[(length(s)-n%width+1):end])
    end
end

function randomFasta(table::Vector{Tuple{String,Float64}}, n::Int64)
    width = 60
    r = (0:width-1)
    gR = Random
    bb = bisect_right
    jn = x -> join(x, "")
    probs::Vector{Float64}, chars::Vector{String} = makeCumulative(table)
    for j in (0:n÷width-1)
        x = jn([chars[bb(probs, gR())] for i in r])
        println(x)
    end
    if (n % width) != 0
        println(jn([chars[bb(probs, gR())] for i in (0:n%width-1)]))
    end
end

function main()
    n = parse(Int, append!([PROGRAM_FILE], ARGS)[2])
    println(">ONE Homo sapiens alu")
    repeatFasta(alu, n * 2)
    println(">TWO IUB ambiguity codes")
    randomFasta(iub, n * 3)
    println(">THREE Homo sapiens frequency")
    randomFasta(homosapiens, n * 5)
end

main()
