# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# contributed by Daniel Jones
# fixed by David Campbell
# modified by Jarret Revels, Alex Arslan, Yichao Yu

using Printf

const variants = [
    "agggtaaa|tttaccct",
    "[cgt]gggtaaa|tttaccc[acg]",
    "a[act]ggtaaa|tttacc[agt]t",
    "ag[act]gtaaa|tttac[agt]ct",
    "agg[act]taaa|ttta[agt]cct",
    "aggg[acg]aaa|ttt[cgt]ccct",
    "agggt[cgt]aa|tt[acg]accct",
    "agggta[cgt]a|t[acg]taccct",
    "agggtaa[cgt]|[acg]ttaccct",
]

const subs = [
    (r"tHa[Nt]", "<4>"),
    (r"aND|caN|Ha[DS]|WaS", "<3>"),
    (r"a[NSt]|BY", "<2>"),
    (r"<[^>]*>", "|"),
    (r"\|[^|][^|]*\|", "-"),
]

function perf_regex_dna()
    seq = read(stdin, String)
    l1 = length(seq)

    seq = replace(seq, r">.*\n|\n" => "")
    l2 = length(seq)

    for v in variants
        k = 0
        for m in eachmatch(Regex(v), seq)
            k += 1
        end
        @printf("%s %d\n", v, k)
    end

    for (u, v) in subs
        seq = replace(seq, u => v)
    end

    println()
    println(l1)
    println(l2)
    println(length(seq))
end

perf_regex_dna()
