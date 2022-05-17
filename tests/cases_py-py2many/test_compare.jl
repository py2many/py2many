using Test


abstract type AbstractEmpty end
abstract type AbstractCmp end
abstract type AbstractComparisonTest end
abstract type AbstractLeft end
abstract type AbstractRight end
abstract type AbstractBase end
abstract type AbstractDerived <: AbstractBase end
abstract type AbstractC end
mutable struct Empty <: AbstractEmpty

end
function __repr__(self::Empty)::String
return "<Empty>"
end

mutable struct Cmp <: AbstractCmp
arg
end
function __repr__(self::Cmp)::String
return "<Cmp %s>" % self.arg
end

function __eq__(self::Cmp, other)::Bool
return self.arg == other
end

mutable struct ComparisonTest <: AbstractComparisonTest
__ne__
candidates::Vector{Union{Complex, Cmp, Float64, Int64}}
set1::Vector{Union{Complex, Cmp, Float64, Int64}}
set2::Vector{Union{Tuple, Empty, Vector{Int64}}}

                    ComparisonTest(__ne__ = unexpected, candidates::Vector{Union{Complex, Cmp, Float64, Int64}} = append!(set1, set2), set1::Vector{Union{Complex, Cmp, Float64, Int64}} = [2, 2.0, 2, 2 + 0im, Cmp(2.0)], set2::Vector{Union{Tuple, Empty, Vector{Int64}}} = [[1], (3,), nothing, Empty()]) =
                        new(__ne__, candidates, set1, set2)
end
function test_comparisons(self::ComparisonTest)
for a in self.candidates
for b in self.candidates
if a ∈ self.set1 && b ∈ self.set1 || a == b
@test (a == b)
else
assertNotEqual(self, a, b)
end
end
end
end

function test_id_comparisons(self::ComparisonTest)
L = []
for i in 0:9
insert(L, length(L) ÷ 2, Empty())
end
for a in L
for b in L
@test (a == b == id(a) == id(b))
end
end
end

function test_ne_defaults_to_not_eq(self::ComparisonTest)
a = Cmp(1)
b = Cmp(1)
c = Cmp(2)
assertIs(self, a == b, true)
assertIs(self, a != b, false)
assertIs(self, a != c, true)
end

function test_ne_high_priority(self::Right)
#= object.__ne__() should allow reflected __ne__() to be tried =#
calls = []
mutable struct Left <: AbstractLeft

end
function __eq__()
push!(calls, "Left.__eq__")
return NotImplemented
end

mutable struct Right <: AbstractRight

end
function __eq__()
push!(calls, "Right.__eq__")
return NotImplemented
end

function __ne__()
push!(calls, "Right.__ne__")
return NotImplemented
end

Left() != Right()
assertSequenceEqual(self, calls, ["Left.__eq__", "Right.__ne__"])
end

function test_ne_low_priority(self::Derived)
#= object.__ne__() should not invoke reflected __eq__() =#
calls = []
mutable struct Base <: AbstractBase

end
function __eq__()
push!(calls, "Base.__eq__")
return NotImplemented
end

mutable struct Derived <: AbstractDerived

end
function __eq__()
push!(calls, "Derived.__eq__")
return NotImplemented
end

function __ne__()
push!(calls, "Derived.__ne__")
return NotImplemented
end

Base() != Derived()
assertSequenceEqual(self, calls, ["Derived.__ne__", "Base.__eq__"])
end

function test_other_delegation(self::C)
#= No default delegation between operations except __ne__() =#
ops = (("__eq__", (a, b) -> a == b), ("__lt__", (a, b) -> a < b), ("__le__", (a, b) -> a <= b), ("__gt__", (a, b) -> a > b), ("__ge__", (a, b) -> a >= b))
for (name, func) in ops
subTest(self, name) do 
function unexpected()
fail(self, "Unexpected operator method called")
end

mutable struct C <: AbstractC
__ne__

                    C(__ne__ = unexpected) =
                        new(__ne__)
end

for (other, _) in ops
if other != name
setattr(C, other, unexpected)
end
end
if name == "__eq__"
assertIs(self, func(C(), object()), false)
else
assertRaises(self, TypeError, func, C(), object())
end
end
end
end

function test_issue_1393(self::ComparisonTest)
x = () -> nothing
@test (x == ALWAYS_EQ)
@test (ALWAYS_EQ == x)
y = object()
@test (y == ALWAYS_EQ)
@test (ALWAYS_EQ == y)
end

function main()
comparison_test = ComparisonTest()
test_comparisons(comparison_test)
test_id_comparisons(comparison_test)
test_ne_defaults_to_not_eq(comparison_test)
test_ne_high_priority(comparison_test)
test_ne_low_priority(comparison_test)
test_other_delegation(comparison_test)
test_issue_1393(comparison_test)
end

main()