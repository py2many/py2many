function main()
(a, b, c) = [1, 2, 3]
println(a);
pairs = [(([2, 2, 2], 2, 2), ([3, 3, 3], 3, 3))]
for (((x1, y1, z1), v1, m1), ((x2, y2, z2), v2, m2)) in pairs
println(x1);
println(y1);
println(z1);
println(x2);
println(y2);
println(z2);
end
end

main()
