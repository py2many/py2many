abstract type AbstractTestClass end
function generator_func()
    Channel() do ch_generator_func
        num = 1
        put!(ch_generator_func, num)
        num = 5
        put!(ch_generator_func, num)
        num = 10
        put!(ch_generator_func, num)
    end
end

function generator_func_loop()
    Channel() do ch_generator_func_loop
        num = 0
        for n = 0:2
            put!(ch_generator_func_loop, num + n)
        end
    end
end

function generator_func_loop_using_var()
    Channel() do ch_generator_func_loop_using_var
        num = 0
        end_ = 2
        end_ = 3
        for n = 0:end_-1
            put!(ch_generator_func_loop_using_var, num + n)
        end
    end
end

function generator_func_nested_loop()
    Channel() do ch_generator_func_nested_loop
        for n = 0:1
            for i = 0:1
                put!(ch_generator_func_nested_loop, (n, i))
            end
        end
    end
end

function file_reader(file_name::String)
    Channel() do ch_file_reader
        for file_row in readline(file_name)
            put!(ch_file_reader, file_row)
        end
    end
end

function testgen()
    Channel() do ch_testgen
        println("first")
        put!(ch_testgen, 1)
        println("second")
        put!(ch_testgen, 2)
    end
end

function fib()
    Channel() do ch_fib
        a = 0
        b = 1
        while true
            put!(ch_fib, a)
            (a, b) = (b, a + b)
        end
    end
end

mutable struct TestClass <: AbstractTestClass

end
function generator_func(self::AbstractTestClass)
    Channel() do ch_generator_func
        num = 123
        put!(ch_generator_func, num)
        num = 5
        put!(ch_generator_func, num)
        num = 10
        put!(ch_generator_func, num)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    arr1 = []
    for i in generator_func()
        push!(arr1, i)
    end
    @assert(arr1 == [1, 5, 10])
    arr2 = []
    for i in generator_func_loop()
        push!(arr2, i)
    end
    @assert(arr2 == [0, 1, 2])
    arr3 = []
    for i in generator_func_loop_using_var()
        push!(arr3, i)
    end
    @assert(arr3 == [0, 1, 2])
    arr4 = []
    testClass1 = TestClass()
    for i in generator_func(testClass1)
        push!(arr4, i)
    end
    @assert(arr4 == [123, 5, 10])
    arr5 = []
    for i in generator_func_nested_loop()
        push!(arr5, i)
    end
    @assert(arr5 == [(0, 0), (0, 1), (1, 0), (1, 1)])
    arr7 = []
    res = fib()
    for i = 0:5
        push!(arr7, take!(res))
    end
    @assert(arr7 == [0, 1, 1, 2, 3, 5])
    for i in testgen()
        println(i)
    end
end
