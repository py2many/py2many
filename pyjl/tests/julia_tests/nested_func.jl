
function test()
    num::Int64 = 2
    teststr::String = "test"
    function inner_test()::String
        return repeat(teststr,num)
    end

    function inner_test_2()::String
        num = 4
        return repeat(teststr,num)
    end

    @assert(inner_test() == "testtest")
    @assert(inner_test_2() == "testtesttesttest")
end

function main()
    test()
end

main()