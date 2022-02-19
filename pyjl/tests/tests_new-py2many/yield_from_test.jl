using ResumableFunctions
 @resumable function generator1()
for i in (0:2)
@yield i;
end
end

function generator()
generator1();
generator2();
end

 @resumable function generator2()
for j in (3:4)
@yield j;
end
end

function main()
arr = []
for i in generator()
push!(arr, i);
end
@assert(arr == [0, 1, 2, 3, 4])
end

main()
