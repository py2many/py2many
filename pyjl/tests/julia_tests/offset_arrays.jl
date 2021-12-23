using OffsetArrays

a1 = [1,2,3,4,5,6]
a0 = OffsetArray(a1, 0:5)

a1[1] == a0[0]

findfirst(==(3), a1)
findfirst(==(3), a0)

function my_find_first(p, a)
    findfirst(p, a)
end

function my_find_first(p, a::OffsetArray)
    findfirst(p, a) - 1
end

println(my_find_first(==(3), a1))
println(my_find_first(==(3), a0))
