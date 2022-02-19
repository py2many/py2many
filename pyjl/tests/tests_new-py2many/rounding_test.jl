using decimal: *
function main()
getcontext().prec = 17
d1 = 4.841431442464721
d2 = -1.1603200440274284
d3 = -0.10362204447112311
println(Decimal(4.841431442464721));
println(d1 == Decimal(4.841431442464721) ? ("True") : ("False"));
end

main()
