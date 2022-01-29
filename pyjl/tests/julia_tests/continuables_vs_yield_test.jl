using ResumableFunctions
using Continuables

function testgen()
    Channel() do ch
        println("first")
        put!(ch, 1)
        println("second")
        put!(ch, 2)
        println("third")
    end
end

@resumable function testgen_res()
    println("first")
    @yield 1
    println("second")
    @yield 2
    println("third")
end

function fib_channels(n::Int)
    Channel() do ch
        a = 0
        b = 1
        for i in 1:n
            put!(ch, a)
            a, b = b, a+b
        end
    end
end

@cont function fib_continuables(n::Int)
    a = 0
    b = 1
    for i in 1:n
      cont(a)
      a, b = b, a+b
    end
end

@resumable function fib_resumable(n::Int) :: Int
    a = 0
    b = 1
    for i in 1:n
      @yield a
      a, b = b, a+b
    end
end
 
function main()
    # Test if all solutions produce the same results
    arr1 = []
    for res in fib_channels(6)
        push!(arr1, res);
    end
    @assert(arr1 == [0,1,1,2,3,5])

    arr2 = []
    for res in collect(fib_continuables(6))
        push!(arr2, res);
    end
    @assert(arr2 == [0,1,1,2,3,5])

    arr3 = []
    for res in fib_resumable(6)
        push!(arr3, res);
    end
    @assert(arr3 == [0,1,1,2,3,5])
end

main()