function generator1()
channel_generator1 = Channel(3)
for i in (0:2)
put!(channel_generator1, i);
end
close(channel_generator1)
channel_generator1
end

function generator()
channel_generator = Channel(5)
for value_generator in generator1()

                        put!(channel_generator, value_generator)
                    end;
for value_generator in generator2()

                        put!(channel_generator, value_generator)
                    end;
close(channel_generator)
channel_generator
end

function generator2()
channel_generator2 = Channel(2)
for j in (3:4)
put!(channel_generator2, j);
end
close(channel_generator2)
channel_generator2
end

function main()
arr = []
for i in generator()
push!(arr, i);
end
@assert(arr == [0, 1, 2, 3, 4])
end

main()
