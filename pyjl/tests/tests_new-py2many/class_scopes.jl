struct ScopeTest
end
function test(self::ScopeTest)::String
return "test"
end

function main()
scope = ScopeTest()
test(scope);
end

main()
