#=  Test Iterator Length Transparency

Some functions or methods which accept general iterable arguments have
optional, more efficient code paths if they know how many items to expect.
For instance, map(func, iterable), will pre-allocate the exact amount of
space required whenever the iterable can report its length.

The desired invariant is:  len(it)==len(list(it)).

A complication is that an iterable and iterator can be the same object. To
maintain the invariant, an iterator needs to dynamically update its length.
For instance, an iterable such as range(10) always reports its length as ten,
but it=iter(range(10)) starts at ten, and then goes to nine after next(it).
Having this capability means that map() can ignore the distinction between
map(func, iterable) and map(func, iter(iterable)).

When the iterable is immutable, the implementation can straight-forwardly
report the original length minus the cumulative number of calls to next().
This is the case for tuples, range objects, and itertools.repeat().

Some containers become temporarily immutable during iteration.  This includes
dicts, sets, and collections.deque.  Their implementation is equally simple
though they need to permanently set their length to zero whenever there is
an attempt to iterate after a length mutation.

The situation slightly more involved whenever an object allows length mutation
during iteration.  Lists and sequence iterators are dynamically updatable.
So, if a list is extended during iteration, the iterator will continue through
the new items.  If it shrinks to a point before the most recent iteration,
then no further items are available and the length is reported at zero.

Reversed objects can also be wrapped around mutable objects; however, any
appends after the current position are ignored.  Any other approach leads
to confusion and possibly returning the same item more than once.

The iterators not listed above, such as enumerate and the other itertools,
are not length transparent because they have no way to distinguish between
iterables that report static length and iterators whose length changes with
each call (i.e. the difference between enumerate('abc') and
enumerate(iter('abc')).

 =#
using Test




abstract type AbstractTestInvariantWithoutMutations end
abstract type AbstractTestTemporarilyImmutable <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestRepeat <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestXrange <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestXrangeCustomReversed <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestTuple <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestDeque <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestDequeReversed <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestDictKeys <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestDictItems <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestDictValues <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestSet <: AbstractTestTemporarilyImmutable end
abstract type AbstractTestList <: AbstractTestInvariantWithoutMutations end
abstract type AbstractTestListReversed <: AbstractTestInvariantWithoutMutations end
abstract type AbstractBadLen <: Abstractobject end
abstract type AbstractBadLengthHint <: Abstractobject end
abstract type AbstractNoneLengthHint <: Abstractobject end
abstract type AbstractTestLengthHintExceptions end
n = 10
mutable struct TestInvariantWithoutMutations <: AbstractTestInvariantWithoutMutations

end
function test_invariant(self::TestInvariantWithoutMutations)
it = self.it
for i in reversed(1:n)
assertEqual(self, length_hint(it), i)
next(it)
end
assertEqual(self, length_hint(it), 0)
assertRaises(self, StopIteration, next, it)
assertEqual(self, length_hint(it), 0)
end

mutable struct TestTemporarilyImmutable <: AbstractTestTemporarilyImmutable

end
function test_immutable_during_iteration(self::TestTemporarilyImmutable)
it = self.it
assertEqual(self, length_hint(it), n)
next(it)
assertEqual(self, length_hint(it), n - 1)
mutate(self)
assertRaises(self, RuntimeError, next, it)
assertEqual(self, length_hint(it), 0)
end

mutable struct TestRepeat <: AbstractTestRepeat
it
end
function setUp(self::TestRepeat)
self.it = repeat(nothing)
end

mutable struct TestXrange <: AbstractTestXrange
it
end
function setUp(self::TestXrange)
self.it = (x for x in 0:n - 1)
end

mutable struct TestXrangeCustomReversed <: AbstractTestXrangeCustomReversed
it
end
function setUp(self::TestXrangeCustomReversed)
self.it = reversed(0:n - 1)
end

mutable struct TestTuple <: AbstractTestTuple
it
end
function setUp(self::TestTuple)
self.it = (x for x in tuple(0:n - 1))
end

mutable struct TestDeque <: AbstractTestDeque
it
mutate
end
function setUp(self::TestDeque)
d = deque(0:n - 1)
self.it = (x for x in d)
self.mutate = d.pop
end

mutable struct TestDequeReversed <: AbstractTestDequeReversed
it
mutate
end
function setUp(self::TestDequeReversed)
d = deque(0:n - 1)
self.it = reversed(d)
self.mutate = d.pop
end

mutable struct TestDictKeys <: AbstractTestDictKeys
it
mutate
end
function setUp(self::TestDictKeys)
d = fromkeys(dict, 0:n - 1)
self.it = (x for x in d)
self.mutate = d.popitem
end

mutable struct TestDictItems <: AbstractTestDictItems
it
mutate
end
function setUp(self::TestDictItems)
d = fromkeys(dict, 0:n - 1)
self.it = (x for x in items(d))
self.mutate = d.popitem
end

mutable struct TestDictValues <: AbstractTestDictValues
it
mutate
end
function setUp(self::TestDictValues)
d = fromkeys(dict, 0:n - 1)
self.it = (x for x in values(d))
self.mutate = d.popitem
end

mutable struct TestSet <: AbstractTestSet
it
mutate
end
function setUp(self::TestSet)
d = set(0:n - 1)
self.it = (x for x in d)
self.mutate = d.pop
end

mutable struct TestList <: AbstractTestList
it
end
function setUp(self::TestList)
self.it = (x for x in 0:n - 1)
end

function test_mutation(self::TestList)
d = collect(0:n - 1)
it = (x for x in d)
next(it)
next(it)
@test (length_hint(it) == n - 2)
push!(d, n)
@test (length_hint(it) == n - 1)
d[2:end] = []
@test (length_hint(it) == 0)
@test (collect(it) == [])
append!(d, 0:19)
@test (length_hint(it) == 0)
end

mutable struct TestListReversed <: AbstractTestListReversed
it
end
function setUp(self::TestListReversed)
self.it = reversed(0:n - 1)
end

function test_mutation(self::TestListReversed)
d = collect(0:n - 1)
it = reversed(d)
next(it)
next(it)
@test (length_hint(it) == n - 2)
push!(d, n)
@test (length_hint(it) == n - 2)
d[2:end] = []
@test (length_hint(it) == 0)
@test (collect(it) == [])
append!(d, 0:19)
@test (length_hint(it) == 0)
end

mutable struct BadLen <: AbstractBadLen

end
function __iter__(self::BadLen)
return (x for x in 0:9)
end

function __len__(self::BadLen)
throw(RuntimeError("hello"))
end

mutable struct BadLengthHint <: AbstractBadLengthHint

end
function __iter__(self::BadLengthHint)
return (x for x in 0:9)
end

function __length_hint__(self::BadLengthHint)
throw(RuntimeError("hello"))
end

mutable struct NoneLengthHint <: AbstractNoneLengthHint

end
function __iter__(self::NoneLengthHint)
return (x for x in 0:9)
end

function __length_hint__(self::NoneLengthHint)
return NotImplemented
end

mutable struct TestLengthHintExceptions <: AbstractTestLengthHintExceptions

end
function test_issue1242657(self::TestLengthHintExceptions)
@test_throws RuntimeError list(BadLen())
@test_throws RuntimeError list(BadLengthHint())
@test_throws RuntimeError [].extend(BadLen())
@test_throws RuntimeError [].extend(BadLengthHint())
b = Vector{UInt8}(0:9)
@test_throws RuntimeError b.extend(BadLen())
@test_throws RuntimeError b.extend(BadLengthHint())
end

function test_invalid_hint(self::TestLengthHintExceptions)
@test (collect(NoneLengthHint()) == collect(0:9))
end

function main()
test_repeat = TestRepeat()
setUp(test_repeat)
test_xrange = TestXrange()
setUp(test_xrange)
test_xrange_custom_reversed = TestXrangeCustomReversed()
setUp(test_xrange_custom_reversed)
test_tuple = TestTuple()
setUp(test_tuple)
test_deque = TestDeque()
setUp(test_deque)
test_deque_reversed = TestDequeReversed()
setUp(test_deque_reversed)
test_dict_keys = TestDictKeys()
setUp(test_dict_keys)
test_dict_items = TestDictItems()
setUp(test_dict_items)
test_dict_values = TestDictValues()
setUp(test_dict_values)
test_set = TestSet()
setUp(test_set)
test_list = TestList()
setUp(test_list)
test_mutation(test_list)
test_list_reversed = TestListReversed()
setUp(test_list_reversed)
test_mutation(test_list_reversed)
test_length_hint_exceptions = TestLengthHintExceptions()
test_issue1242657(test_length_hint_exceptions)
test_invalid_hint(test_length_hint_exceptions)
end

main()