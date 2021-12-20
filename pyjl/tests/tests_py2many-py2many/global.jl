code_0 = 0
code_1 = 1
l_a = [code_0, code_1]
code_a = "a"
code_b = "b"
l_b = [code_a, code_b]
function main()
    for i in l_a
        println(i)
    end
    for j in l_b
        println(j)
    end
    if "a" in ["a", "b"]
        println("OK")
    end
end

main()
