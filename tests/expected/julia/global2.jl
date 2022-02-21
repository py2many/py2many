code_0 = 0
code_1 = 1
code_a = "a"
code_b = "b"
l_b = Set([code_a])
l_c = Dict(code_b => code_0)
function main()
    @assert("a" in l_b)
    println(join(["OK"], " "))
end

main()
