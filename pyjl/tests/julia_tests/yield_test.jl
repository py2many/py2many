using ResumableFunctions
using Continuables

function gen()
    Channel() do ch
        println("before")
        put!(ch, 1)
        println("after")
        put!(ch, 2)
    end
end

function gen_2()
    Channel(1) do ch
        println("before")
        put!(ch, 1)
        println("after")
        put!(ch, 2)
    end
end

@resumable function testgen_res()
    println("first")
    @yield 1
    println("second")
    @yield 2
    println("third")
end

###########################
# Fibonacci Implementations

function fib_channels()
    Channel() do ch
        a = 0
        b = 1
        println("Side-effect")
        while true
            put!(ch, a)
            a, b = b, a+b
        end
    end
end

@cont function fib_continuables()
    a = 0
    b = 1
    println("Side-effect")
    while true
        cont(a)
        a, b = b, a+b
    end
end

@resumable function fib_resumable() :: Int
    a = 0
    b = 1
    println("Side-effect")
    while true
        @yield a
        a, b = b, a + b
    end
end
 
function main()
    # Test if all solutions produce the same results
    arr1 = []
    res = fib_channels()
    for i in 1:6
        push!(arr1, take!(res));
    end
    @assert(arr1 == [0,1,1,2,3,5])

    arr2 = collect(take(6, fib_continuables()))
    @assert(arr2 == [0,1,1,2,3,5])

    arr3 = []
    f = fib_resumable()
    for i in 1:6
        push!(arr3, f());
    end
    @assert(arr3 == [0,1,1,2,3,5])

    for x in gen()
        println(x)
    end
    for x in gen_2()
        println(x)
    end

    println("-----------------------")
    let it = gen()
        println(0)
        for x in it
            println(x)
        end
    end
end

main()