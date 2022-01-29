using Continuables
function generator_func()
c_generator_func = Channel(3)
num = 1
put!(c_generator_func, num);
num = 5
put!(c_generator_func, num);
num = 10
put!(c_generator_func, num);
close(c_generator_func)
return c_generator_func
end

function generator_func_loop()
c_generator_func_loop = Channel(1)
num = 0
t_generator_func_loop = @async for n in (0:2)
put!(c_generator_func_loop, num + n);
end
bind(c_generator_func_loop, t_generator_func_loop)
end

function generator_func_loop_using_var()
c_generator_func_loop_using_var = Channel(1)
num = 0
end_ = 2
end_ = 3
t_generator_func_loop_using_var = @async for n in (0:end_ - 1)
put!(c_generator_func_loop_using_var, num + n);
end
bind(c_generator_func_loop_using_var, t_generator_func_loop_using_var)
end

function generator_func_nested_loop()
c_generator_func_nested_loop = Channel(1)
t_generator_func_nested_loop = @async for n in (0:1)
for i in (0:1)
put!(c_generator_func_nested_loop, (n, i));
end
end
bind(c_generator_func_nested_loop, t_generator_func_nested_loop)
end

@cont function file_reader(file_name::String)
for file_row in readline(file_name)
cont(file_row);
end
end

function testgen()
    Channel(1) do ch
        println("first")
        for i in 1:2
            put!(ch, 1)
        end
        println("second")
        put!(ch, 2)
    end
end

struct TestClass
end
function generator_func(self::TestClass)
c_generator_func = Channel(3)
num = 123
put!(c_generator_func, num);
num = 5
put!(c_generator_func, num);
num = 10
put!(c_generator_func, num);
close(c_generator_func)
return c_generator_func
end

function main()
arr1 = []
for i in generator_func()
push!(arr1, i);
end
@assert(arr1 == [1, 5, 10])
arr2 = []
for i in generator_func_loop()
push!(arr2, i);
end
@assert(arr2 == [0, 1, 2])
arr3 = []
for i in generator_func_loop_using_var()
push!(arr3, i);
end
@assert(arr3 == [0, 1, 2])
arr4 = []
testClass1::TestClass = TestClass()
for i in generator_func(testClass1)
push!(arr4, i);
end
@assert(arr4 == [123, 5, 10])
arr5 = []
for i in generator_func_nested_loop()
push!(arr5, i);
end
@assert(arr5 == [(0, 0), (0, 1), (1, 0), (1, 1)])
arr6 = []
for res in collect(file_reader("C:/Users/Miguel Marcelino/Desktop/test.txt"))
push!(arr6, res);
end
@assert(arr6 == ["test\n", "test\n", "test"])
for i in collect(testgen())
println(i);
end
end

main()
