function generator_func()
channel_generator_func = Channel(3)
num = 1
put!(channel_generator_func, num);
num = 5
put!(channel_generator_func, num);
num = 10
put!(channel_generator_func, num);
close((channel_generator_func))
return channel_generator_func
end

function generator_func_loop()
channel_generator_func_loop = Channel(3)
num = 0
for n in (0:2)
put!(channel_generator_func_loop, num + n);
end
close((channel_generator_func_loop))
return channel_generator_func_loop
end

function generator_func_loop_using_var()
channel_generator_func_loop_using_var = Channel(3)
num = 0
end_ = 2
end_ = 3
for n in (0:end_ - 1)
put!(channel_generator_func_loop_using_var, num + n);
end
close((channel_generator_func_loop_using_var))
return channel_generator_func_loop_using_var
end

function generator_func_nested_loop()
channel_generator_func_nested_loop = Channel(4)
for n in (0:1)
for i in (0:1)
put!(channel_generator_func_nested_loop, (n, i));
end
end
close((channel_generator_func_nested_loop))
return channel_generator_func_nested_loop
end

struct TestClass
end
function generator_func(self::TestClass)
channel_generator_func = Channel(3)
num = 123
put!(channel_generator_func, num);
num = 5
put!(channel_generator_func, num);
num = 10
put!(channel_generator_func, num);
close((channel_generator_func))
return channel_generator_func
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
end

main()
