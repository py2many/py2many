using Distributed

function init(arg)
    global seq
    seq = arg
end

function var_find(f)::Int64
    return length(findall(f, seq))
end

function main_func()
    seq = read(stdin)
    ilen = length(seq)
    seq = replace(seq, r">.*\n|\n" => s"")
    clen = length(seq)
    pool = default_worker_pool()
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
    for f in zip(variants, imap(pool, var_find, variants))
        println(f[1], f[2])
    end
    subst = Dict(
        "tHa[Nt]" => "<4>",
        "aND|caN|Ha[DS]|WaS" => "<3>",
        "a[NSt]|BY" => "<2>",
        "<[^>]*>" => "|",
        "\\|[^|][^|]*\\|" => "-",
    )
    for (f, r) in collect(items(subst))
        seq = replace(seq, rf => sr)
    end
    println()
    println(ilen)
    println(clen)
    println(length(seq))
end

function main()
    main_func()
end

main()
