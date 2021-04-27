
function indexing()::Int64
    sum = 0
    a::Array{Int64} = []
    for i in (0:10-1)
        push!(a, i)
        sum += a[i+1]
    end
    return sum
end

function show()
    a1 = 10
    a2::Float64 = 2.1
    println(join([a2], " "))
    for i in (0:10-1)
        println(join([i], " "))
    end
    for i in (0:2:10-1)
        println(join([i], " "))
    end
    a3 = -(a1)
    a4 = (a3 + a1)
    println(join([a4], " "))
    sum1 = indexing()
    println(join([sum1], " "))
    a5 = [1, 2, 3]
    println(join([length(a5)], " "))
    a9::Array{String} = ["a", "b", "c", "d"]
    println(join([length(a9)], " "))
    if 1 != nothing
        println(join(["World is sane"], " "))
    end
end

function main()
    show()
end

main()
