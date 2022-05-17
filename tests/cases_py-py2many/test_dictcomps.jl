using Test

abstract type AbstractDictComprehensionTest end
g = "Global variable"
mutable struct DictComprehensionTest <: AbstractDictComprehensionTest

end
function test_basics(self::DictComprehensionTest)
expected = Dict(0 => 10, 1 => 11, 2 => 12, 3 => 13, 4 => 14, 5 => 15, 6 => 16, 7 => 17, 8 => 18, 9 => 19)
actual = Dict(k => k + 10 for k in 0:9)
@test (actual == expected)
expected = Dict(0 => 0, 1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5, 6 => 6, 7 => 7, 8 => 8, 9 => 9)
actual = Dict(k => v for k in 0:9 for v in 0:9 if k == v )
@test (actual == expected)
end

function test_scope_isolation(self::DictComprehensionTest)
k = "Local Variable"
expected = Dict(0 => nothing, 1 => nothing, 2 => nothing, 3 => nothing, 4 => nothing, 5 => nothing, 6 => nothing, 7 => nothing, 8 => nothing, 9 => nothing)
actual = Dict(k => nothing for k in 0:9)
@test (actual == expected)
@test (k == "Local Variable")
expected = Dict(9 => 1, 18 => 2, 19 => 2, 27 => 3, 28 => 3, 29 => 3, 36 => 4, 37 => 4, 38 => 4, 39 => 4, 45 => 5, 46 => 5, 47 => 5, 48 => 5, 49 => 5, 54 => 6, 55 => 6, 56 => 6, 57 => 6, 58 => 6, 59 => 6, 63 => 7, 64 => 7, 65 => 7, 66 => 7, 67 => 7, 68 => 7, 69 => 7, 72 => 8, 73 => 8, 74 => 8, 75 => 8, 76 => 8, 77 => 8, 78 => 8, 79 => 8, 81 => 9, 82 => 9, 83 => 9, 84 => 9, 85 => 9, 86 => 9, 87 => 9, 88 => 9, 89 => 9)
actual = Dict(k => v for v in 0:9 for k in v*9:v*10)
@test (k == "Local Variable")
@test (actual == expected)
end

function test_scope_isolation_from_global(self::DictComprehensionTest)
expected = Dict(0 => nothing, 1 => nothing, 2 => nothing, 3 => nothing, 4 => nothing, 5 => nothing, 6 => nothing, 7 => nothing, 8 => nothing, 9 => nothing)
actual = Dict(g => nothing for g in 0:9)
@test (actual == expected)
@test (g == "Global variable")
expected = Dict(9 => 1, 18 => 2, 19 => 2, 27 => 3, 28 => 3, 29 => 3, 36 => 4, 37 => 4, 38 => 4, 39 => 4, 45 => 5, 46 => 5, 47 => 5, 48 => 5, 49 => 5, 54 => 6, 55 => 6, 56 => 6, 57 => 6, 58 => 6, 59 => 6, 63 => 7, 64 => 7, 65 => 7, 66 => 7, 67 => 7, 68 => 7, 69 => 7, 72 => 8, 73 => 8, 74 => 8, 75 => 8, 76 => 8, 77 => 8, 78 => 8, 79 => 8, 81 => 9, 82 => 9, 83 => 9, 84 => 9, 85 => 9, 86 => 9, 87 => 9, 88 => 9, 89 => 9)
actual = Dict(g => v for v in 0:9 for g in v*9:v*10)
@test (g == "Global variable")
@test (actual == expected)
end

function test_global_visibility(self::DictComprehensionTest)
expected = Dict(0 => "Global variable", 1 => "Global variable", 2 => "Global variable", 3 => "Global variable", 4 => "Global variable", 5 => "Global variable", 6 => "Global variable", 7 => "Global variable", 8 => "Global variable", 9 => "Global variable")
actual = Dict(k => g for k in 0:9)
@test (actual == expected)
end

function test_local_visibility(self::DictComprehensionTest)
v = "Local variable"
expected = Dict(0 => "Local variable", 1 => "Local variable", 2 => "Local variable", 3 => "Local variable", 4 => "Local variable", 5 => "Local variable", 6 => "Local variable", 7 => "Local variable", 8 => "Local variable", 9 => "Local variable")
actual = Dict(k => v for k in 0:9)
@test (actual == expected)
@test (v == "Local variable")
end

function test_illegal_assignment(self::DictComprehensionTest)
assertRaisesRegex(self, SyntaxError, "cannot assign") do 
compile("{x: y for y, x in ((1, 2), (3, 4))} = 5", "<test>", "exec")
end
assertRaisesRegex(self, SyntaxError, "illegal expression") do 
compile("{x: y for y, x in ((1, 2), (3, 4))} += 5", "<test>", "exec")
end
end

function test_evaluation_order(self::DictComprehensionTest)
expected = Dict("H" => "W", "e" => "o", "l" => "l", "o" => "d")
expected_calls = [("key", "H"), ("value", "W"), ("key", "e"), ("value", "o"), ("key", "l"), ("value", "r"), ("key", "l"), ("value", "l"), ("key", "o"), ("value", "d")]
actual_calls = []
function add_call(pos, value)
push!(actual_calls, (pos, value))
return value
end

actual = Dict(add_call("key", k) => add_call("value", v) for (k, v) in zip(["H", "e", "l", "l", "o"], "World"))
@test (actual == expected)
@test (actual_calls == expected_calls)
end

function test_assignment_idiom_in_comprehensions(self::DictComprehensionTest)
expected = Dict(1 => 1, 2 => 4, 3 => 9, 4 => 16)
actual = Dict(j => j*j for i in 0:3 for j in [i + 1])
@test (actual == expected)
expected = Dict(3 => 2, 5 => 6, 7 => 12, 9 => 20)
actual = Dict(j + k => j*k for i in 0:3 for j in [i + 1] for k in [j + 1])
@test (actual == expected)
expected = Dict(3 => 2, 5 => 6, 7 => 12, 9 => 20)
actual = Dict(j + k => j*k for i in 0:3 for (j, k) in [(i + 1, i + 2)])
@test (actual == expected)
end

function test_star_expression(self::DictComprehensionTest)
expected = Dict(0 => 0, 1 => 1, 2 => 4, 3 => 9)
@test (Dict(i => i*i for i in [0:3...]) == expected)
@test (Dict(i => i*i for i in (0:3...,)) == expected)
end

function main()
dict_comprehension_test = DictComprehensionTest()
test_basics(dict_comprehension_test)
test_scope_isolation(dict_comprehension_test)
test_scope_isolation_from_global(dict_comprehension_test)
test_global_visibility(dict_comprehension_test)
test_local_visibility(dict_comprehension_test)
test_illegal_assignment(dict_comprehension_test)
test_evaluation_order(dict_comprehension_test)
test_assignment_idiom_in_comprehensions(dict_comprehension_test)
test_star_expression(dict_comprehension_test)
end

main()