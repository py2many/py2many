using Test



abstract type Abstractbase_set end
abstract type Abstractmyset <: Abstractbase_set end
abstract type Abstractseq <: Abstractbase_set end
abstract type AbstractTestContains end
abstract type AbstractDeviant1 end
abstract type AbstractByContains <: Abstractobject end
abstract type AbstractBlockContains <: AbstractByContains end
mutable struct base_set <: Abstractbase_set
el
end

mutable struct myset <: Abstractmyset
el
end
function __contains__(self::myset, el)::Bool
return self.el == el
end

mutable struct seq <: Abstractseq
el
end
function __getitem__(self::seq, n)
return [self.el][n + 1]
end

mutable struct TestContains <: AbstractTestContains
__contains__
aList::Vector

                    TestContains(__contains__ = nothing, aList::Vector = collect(0:14)) =
                        new(__contains__, aList)
end
function test_common_tests(self::TestContains)
a = base_set(1)
b = myset(1)
c = seq(1)
assertIn(self, 1, b)
assertNotIn(self, 0, b)
assertIn(self, 1, c)
assertNotIn(self, 0, c)
@test_throws TypeError () -> 1 ∈ a()
@test_throws TypeError () -> 1 ∉ a()
assertIn(self, "c", "abc")
assertNotIn(self, "d", "abc")
assertIn(self, "", "")
assertIn(self, "", "abc")
@test_throws TypeError () -> nothing ∈ "abc"()
end

function test_builtin_sequence_types(self::Deviant1)
a = 0:9
for i in a
assertIn(self, i, a)
end
assertNotIn(self, 16, a)
assertNotIn(self, a, a)
a = tuple(a)
for i in a
assertIn(self, i, a)
end
assertNotIn(self, 16, a)
assertNotIn(self, a, a)
mutable struct Deviant1 <: AbstractDeviant1
#= Behaves strangely when compared

            This class is designed to make sure that the contains code
            works when the list is modified during the check.
             =#
aList::Vector

                    Deviant1(aList::Vector = collect(0:14)) =
                        new(aList)
end
function __eq__(self::Deviant1, other)::Int64
if other == 12
remove(self.aList, 12)
remove(self.aList, 13)
remove(self.aList, 14)
end
return 0
end

assertNotIn(self, Deviant1(), Deviant1.aList)
end

function test_nonreflexive(self::TestContains)
values = (float("nan"), 1, nothing, "abc", NEVER_EQ)
constructors = (list, tuple, dict.fromkeys, set, frozenset, deque)
for constructor in constructors
container = constructor(values)
for elem in container
assertIn(self, elem, container)
end
@test container == constructor(values)
@test container == container
end
end

function test_block_fallback(self::BlockContains)
mutable struct ByContains <: AbstractByContains

end
function __contains__(self::ByContains, other)::Bool
return false
end

c = ByContains()
mutable struct BlockContains <: AbstractBlockContains
#= Is not a container

            This class is a perfectly good iterable (as tested by
            list(bc)), as well as inheriting from a perfectly good
            container, but __contains__ = None prevents the usual
            fallback to iteration in the container protocol. That
            is, normally, 0 in bc would fall back to the equivalent
            of any(x==0 for x in bc), but here it's blocked from
            doing so.
             =#
__contains__

                    BlockContains(__contains__ = nothing) =
                        new(__contains__)
end
function __iter__(self::BlockContains)
Channel() do ch___iter__ 
while false
put!(ch___iter__, nothing)
end
end
end

bc = BlockContains()
assertFalse(self, 0 ∈ c)
assertFalse(self, 0 ∈ collect(bc))
assertRaises(self, TypeError, () -> 0 ∈ bc)
end

function main()
test_contains = TestContains()
test_common_tests(test_contains)
test_builtin_sequence_types(test_contains)
test_nonreflexive(test_contains)
test_block_fallback(test_contains)
end

main()