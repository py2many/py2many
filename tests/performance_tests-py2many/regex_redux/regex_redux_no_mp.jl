using OrderedCollections

function var_find(f)::Int64
    return length(collect(eachmatch(Regex(f), seq)))
end

function main()
    global seq
    seq = read(stdin, String)
    ilen = length(seq)
    seq = replace(seq, r">.*\n|\n" => s"")
    clen = length(seq)
    variants = (
        "agggtaaa|tttaccct",
        "[cgt]gggtaaa|tttaccc[acg]",
        "a[act]ggtaaa|tttacc[agt]t",
        "ag[act]gtaaa|tttac[agt]ct",
        "agg[act]taaa|ttta[agt]cct",
        "aggg[acg]aaa|ttt[cgt]ccct",
        "agggt[cgt]aa|tt[acg]accct",
        "agggta[cgt]a|t[acg]taccct",
        "agggtaa[cgt]|[acg]ttaccct",
    )
    for f in zip(variants, map(var_find, variants))
        println("$(f[1])$(f[2])")
    end
    subst = OrderedDict(
        "tHa[Nt]" => "<4>",
        "aND|caN|Ha[DS]|WaS" => "<3>",
        "a[NSt]|BY" => "<2>",
        "<[^>]*>" => "|",
        "\\|[^|][^|]*\\|" => "-",
    )
    for (f, r) in collect(subst)
        seq = replace(seq, Regex(f) => SubstitutionString(r))
    end
    println()
    println(ilen)
    println(clen)
    println(length(seq))
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
