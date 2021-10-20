using Continuables
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

function main()
for i in collect(generator_func())
println(i);
end
println("-----------------------");
for i in generator_func_loop()
println(i);
end
end

main()
