@cont function generator_func()
num = 1
cont(num);
num = 5
cont(num);
num = 10
cont(num);
end

 function main()
for i in generator_func()
println(i);
end
end

main()
