code_0 = 0
code_1 = 1
l_a = [code_0, code_1]
code_a = "a"
code_b = "b"
l_b = [code_a, code_b]
function main()
    for i in l_a
        println(join([i], " "))
    end
    for j in l_b
        println(join([j], " "))
    end
    if "a" in ["a", "b"]
        println(join(["OK"], " "))
    end
end

main()
