function main()
l = [1, 2, 3]
b = ["a", "b", "c"]
x = 0
ll = l[(x + 1 + 1):end]
x = 1
lb = b[(x + 1 + 1):end]
@assert(ll == [2, 3])
@assert(lb == ["c"])
println("OK");
end

main()
