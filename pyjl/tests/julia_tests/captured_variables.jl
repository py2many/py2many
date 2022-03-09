# Full discussion at: 
# https://docs.julialang.org/en/v1/manual/performance-tips/#man-performance-captured

function abmult1(r::Int)
    if r < 0
        r = -r
    end
    f = x -> x * r
    return f
end

# Still not full performance: 
# r still has to change in f when changed in an outer scope
function abmult2(r0::Int)
    r::Int = r0
    if r < 0
        r = -r
    end
    f = x -> x * r
    return f
end

# Retains full performance
# An alternative is to use the FastClosures package
function abmult3(r::Int)
    if r < 0
        r = -r
    end
    f = let r = r
            x -> x * r
    end
    return f
end

# @code_warntype abmult1(1)
# @code_warntype abmult2(1)
@code_warntype abmult3(1)