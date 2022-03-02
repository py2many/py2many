abstract type AbstractTestClass end
function func()::String
    return "test"
end


struct TestClass <: AbstractTestClass

end
function func(self::AbstractTestClass)::String
    return "test2"
end


function test()
    num::Int64 = 2
    teststr::String = "test"
    function inner_test()::String
        return repeat(teststr, num)
    end

    function inner_test_2()::String
        num = 4
        return num * teststr
    end

    @assert(inner_test() == "testtest")
    @assert(inner_test_2() == "testtesttesttest")
end

function main()
    @assert(func() == "test")
    testClass = TestClass()
    @assert(func(testClass) == "test2")
    test()
end

main()
