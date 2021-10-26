using Continuables
using DataClass
@cont function generator_func()
num = 1
cont(num);
num = 5
cont(num);
num = 10
cont(num);
end

function generator_func_loop()
channel_generator_func_loop = Channel(9)
num = 0
for n in (1:10 - 1)
put!(channel_generator_func_loop, (num + n));
end
close(channel_generator_func_loop)
channel_generator_func_loop
end

function generator_func_loop_using_var()
channel_generator_func_loop_using_var = Channel(15)
num = 0
end_ = 12
end_ = 16
for n in (1:end_ - 1)
put!(channel_generator_func_loop_using_var, (num + n));
end
close(channel_generator_func_loop_using_var)
channel_generator_func_loop_using_var
end

@dataclass mutable struct TestClass
end
@cont function generator_func(self::TestClass, ola::Int64)
num = 1
cont(num);
num = 5
cont(num);
num = 10
cont(num);
end


function main()
for i in collect(generator_func())
println(i);
end
println("-----------------------");
for i in generator_func_loop()
println(i);
end
println("-----------------------");
for i in generator_func_loop_using_var()
println(i);
end
println("-----------------------");
testClass = TestClass()
for i in collect(generator_func())
println(i);
end
end

main()
