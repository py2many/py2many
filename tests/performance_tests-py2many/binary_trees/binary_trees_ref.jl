# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# Contributed by Joonas Muhonen. Based on code by Adam Beckmeyer, Jarret Revels, Alex
# Arslan, Michal Stransky, Jens Adam.

using BenchmarkTools

struct Node
    l::Union{Node, Nothing}
    r::Union{Node, Nothing}
end

mutable struct Latch
    count::Int
    cond::Threads.Condition
end

function Latch(n::Int)::Latch
    Latch(n, Threads.Condition())
end

function countDown(latch::Latch)
    lock(latch.cond) do
        latch.count -= 1
        notify(latch.cond)
    end
end

function await(latch::Latch)
    lock(latch.cond)
    try
        while latch.count != 0
            wait(latch.cond)
        end
    finally
        unlock(latch.cond)
    end
end

function make(n::Int)::Node
    n === 0 ? Node(nothing, nothing) : Node(make(n - 1), make(n - 1))
end

function check(node::Node)::Int
    node.l === nothing ? 1 : 1 + check(node.l) + check(node.r)
end

function binary_trees(io, n::Int)
    write(io, "stretch tree of depth $(n+1)\t check: $(check(make(n+1)))\n")

    long_tree::Node = make(n)

    minDepth::Int = 4
    resultSize::Int = trunc(Int, (n - minDepth) / 2) + 1
    results = Vector{String}(undef, resultSize)
    latch::Latch = Latch(resultSize)
    Threads.@threads for depth::Int = minDepth:2:n
        c::Int = 0
        niter::Int = 1 << (n - depth + minDepth)
        lk::ReentrantLock = ReentrantLock()
        # Is this required/helpful?
        Threads.@threads for _ = 1:niter
            lock(lk) do
                c += check(make(depth))
            end
        end#for
        index::Int = trunc(Int, (depth - minDepth) / 2) + 1
        results[index] = "$niter\t trees of depth $depth\t check: $c\n"
        countDown(latch)
    end
    await(latch)
    for i in results
        write(io, i)
    end

    write(io, "long lived tree of depth $n\t check: $(check(long_tree))\n")
end#function

isinteractive() || binary_trees(stdout, parse(Int, ARGS[1]))

# Benchmarks
# ARGS = ["21"]
# BenchmarkTools.DEFAULT_PARAMETERS.samples = 10
# BenchmarkTools.DEFAULT_PARAMETERS.evals = 2
# BenchmarkTools.DEFAULT_PARAMETERS.seconds = 150
# @benchmark binary_trees(stdout, parse(Int, ARGS[1])) # @benchmark 
