function func()::String
return "aaaa"
end

struct TestClass
end
function func(self::TestClass)::String
return "ssss"
end


function main()
println(func());
testClass = TestClass()
println(testClass.func());
end

main()
