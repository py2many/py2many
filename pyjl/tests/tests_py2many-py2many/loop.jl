function for_with_break()
arr = []
for i in (0:3)
if i == 2
break;
end
push!(arr, i);
end
@assert(arr == [0, 1])
end

function for_with_continue()
arr = []
for i in (0:3)
if i == 2
continue;
end
push!(arr, i);
end
@assert(arr == [0, 1, 3])
end

function for_with_else()
arr = []
for i in (0:3)
push!(arr, i);
end
@assert(arr == [0, 1, 2, 3, 4])
end

function while_with_break()
arr = []
i = 0
while true
if i == 2
break;
end
push!(arr, i);
i += 1
end
@assert(arr == [0, 1])
end

function while_with_continue()
arr = []
i = 0
while i < 5
i += 1
if i == 2
continue;
end
push!(arr, i);
end
@assert(arr == [1, 3, 4, 5])
end

function loop_range_test()
arr1 = []
for i in (1:9)
push!(arr1, i);
end
arr2 = []
num = (1:11)
for i in num
push!(arr2, i);
end
@assert(arr1 == [1, 2, 3, 4, 5, 6, 7, 8, 9])
@assert(arr2 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
end

function loop_element_test()
arr = [1, 2, 3]
arr1 = []
for e in arr
e[2];
push!(arr1, e);
end
@assert(arr1 == [1, 2, 3])
end

function loop_element_test_2()
arr = [1, 2]
arr_c = [2, 3, 4]
arr1 = []
for e in arr
push!(arr1, arr_c[e + 1]);
end
@assert(arr1 == [3, 4])
end

function main()
for_with_break();
for_with_continue();
while_with_break();
while_with_continue();
loop_range_test();
loop_element_test_2();
end

main()
