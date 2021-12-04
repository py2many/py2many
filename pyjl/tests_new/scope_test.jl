function func()::String
return "aaaa"
end

struct TestClass
end
function func(self::TestClass)::String
return "ssss"
end


function test()
num::Int64 = 2
teststr::String = "ola"
function inner_test()
println(repeat(teststr,num));
end

function inner_test_2()
num::Int64 = 4
println(repeat(teststr,num));
end

inner_test();
inner_test_2();
end

function main()
println(func());
testClass = TestClass()
println(func(testClass));
test();
end

main()
