using Distributed




function eval_A(i::Any, j::Any)::Int64
    ij = i + j
    return ((ij * (ij + 1) ÷ 2) + i) + 1
end

function A_sum(u::Any, i::Any)
    return sum((u_j / eval_A(i, j) for (j, u_j) in enumerate(u)))
end

function At_sum(u::Any, i::Any)
    return sum((u_j / eval_A(j, i) for (j, u_j) in enumerate(u)))
end

function multiply_AtAv(u::Any)
    r = 0:length(u)-1
    tmp = pmap(A_sum, zip(repeat(u), r))
    return pmap(At_sum, zip(repeat(tmp), r))
end

function main_func()
    n = 10
    u = repeat([1], n)
    for _ = 0:9
        v = multiply_AtAv(u)
        u = multiply_AtAv(v)
    end
    vBv = 0
    vv = 0
    for (ue, ve) in zip(u, v)
        vBv += ue * ve
        vv += ve * ve
    end
    result = √(vBv / vv)
    println("{0:.9f}")
end

function main()
    default_worker_pool() do pool
        main_func()
    end
end

main()
