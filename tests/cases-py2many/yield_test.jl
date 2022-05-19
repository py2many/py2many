using ResumableFunctions
abstract type AbstractTestClass end
@resumable function generator_func()
    num = 1
    @yield num
    num = 5
    @yield num
    num = 10
    @yield num
end

@resumable function generator_func_loop()
    num = 0
    for n = 0:2
        @yield num + n
    end
end

@resumable function generator_func_loop_using_var()
    num = 0
    end_ = 2
    end_ = 3
    for n = 0:end_-1
        @yield num + n
    end
end

@resumable function generator_func_nested_loop()
    for n = 0:1
        for i = 0:1
            @yield (n, i)
        end
    end
end

@resumable function file_reader(file_name::String)
    for file_row in readline(file_name)
        @yield file_row
    end
end

@resumable function testgen()
    println("first")
    @yield 1
    println("second")
    @yield 2
end

@resumable function fib()
    a = 0
    b = 1
    while true
        @yield a
        a, b = (b, a + b)
    end
end

mutable struct TestClass <: AbstractTestClass
end
@resumable function generator_func(self::TestClass)
    num = 123
    @yield num
    num = 5
    @yield num
    num = 10
    @yield num
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
    testClass1::TestClass = TestClass()
    for i in generator_func(testClass1)
        push!(arr4, i)
    end
    @assert(arr4 == [123, 5, 10])
    arr5 = []
    for i in generator_func_nested_loop()
        push!(arr5, i)
    end
    @assert(arr5 == [(0, 0), (0, 1), (1, 0), (1, 1)])
    arr6 = []
    for res in file_reader("C:/Users/Miguel Marcelino/Desktop/test.txt")
        push!(arr6, res)
    end
    @assert(arr6 == ["test\n", "test\n", "test"])
    arr7 = []
    res = fib()
    for i = 0:5
        push!(arr7, res)
    end
    @assert(arr7 == [0, 1, 1, 2, 3, 5])
    for i in testgen()
        println(i)
    end
end
