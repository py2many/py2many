function generator1()
c_generator1 = Channel(1)
t_generator1 = @async for i in (0:2)
put!(c_generator1, i);
end
bind(c_generator1, t_generator1)
end

function generator()
c_generator = Channel(1)
t_generator = @async for v_generator in generator1()
put!(c_generator, v_generator)
end;
t_generator = @async for v_generator in generator2()
put!(c_generator, v_generator)
end;
bind(c_generator, t_generator)
end

function generator2()
c_generator2 = Channel(1)
t_generator2 = @async for j in (3:4)
put!(c_generator2, j);
end
bind(c_generator2, t_generator2)
end

function main()
arr = []
for i in generator()
push!(arr, i);
end
@assert(arr == [0, 1, 2, 3, 4])
end

main()
