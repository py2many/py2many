abstract type AbstractTestClass end
function func()::String
    return "test"
end

mutable struct TestClass <: AbstractTestClass
end
function func(self::TestClass)::String
    return "test2"
end

function test()
    num::Int64 = 2
    teststr::String = "test"
    function inner_test()::String
        return repeat(teststr, num)
    end

    function inner_test_2(num)::String
        return num * teststr
    end

    @assert(inner_test() == "testtest")
    @assert(inner_test_2(4) == "testtesttesttest")
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(func() == "test")
    testClass = TestClass()
    @assert(func(testClass) == "test2")
    test()
end
