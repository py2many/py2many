using Test





abstract type AbstractListTest <: Abstractlist_tests.CommonTest end
abstract type AbstractL <: Abstractlist end
abstract type AbstractX end
abstract type AbstractY end
abstract type AbstractZ end
mutable struct ListTest <: AbstractListTest
type2test

                    ListTest(type2test = list) =
                        new(type2test)
end
function test_basic(self::ListTest)
@test (collect([]) == [])
l0_3 = [0, 1, 2, 3]
l0_3_bis = collect(l0_3)
@test (l0_3 == l0_3_bis)
@test l0_3 != l0_3_bis
@test (collect(()) == [])
@test (collect((0, 1, 2, 3)) == [0, 1, 2, 3])
@test (collect("") == [])
@test (collect("spam") == ["s", "p", "a", "m"])
@test (collect((x for x in 0:9 if x % 2 )) == [1, 3, 5, 7, 9])
if sys.maxsize == 2147483647
@test_throws MemoryError list(0:sys.maxsize ÷ 2)
end
x = []
append!(x, (-(y) for y in x))
@test (x == [])
end

function test_keyword_args(self::ListTest)
assertRaisesRegex(self, TypeError, "keyword argument") do 
collect([])
end
end

function test_truth(self::ListTest)
test_truth(super())
@test !([])
@test [42]
end

function test_identity(self::ListTest)
@test [] != []
end

function test_len(self::ListTest)
test_len(super())
@test (length([]) == 0)
@test (length([0]) == 1)
@test (length([0, 1, 2]) == 3)
end

function test_overflow(self::ListTest)
lst = [4, 5, 6, 7]
n = Int((sys.maxsize*2 + 2) ÷ length(lst))
function mul(a, b)::Any
return a*b
end

function imul(a, b)
a *= b
end

@test_throws (MemoryError, OverflowError) mul(lst, n)
@test_throws (MemoryError, OverflowError) imul(lst, n)
end

function test_repr_large(self::ListTest)
function check(n)
l = [0]*n
s = repr(l)
@test (s == ("[" + join(["0"]*n, ", ")) * "]")
end

check(10)
check(1000000)
end

function test_iterator_pickle(self::ListTest)
orig = type2test(self, [4, 5, 6, 7])
data = [10, 11, 12, 13, 14, 15]
for proto in 0:pickle.HIGHEST_PROTOCOL
itorig = (x for x in orig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data)
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[2:end])
for i in 1:length(orig) - 1
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[length(orig) + 1:end])
@test_throws StopIteration next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (collect(it) == [])
end
end

function test_reversed_pickle(self::ListTest)
orig = type2test(self, [4, 5, 6, 7])
data = [10, 11, 12, 13, 14, 15]
for proto in 0:pickle.HIGHEST_PROTOCOL
itorig = reversed(orig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[end:-1:length(orig)])
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[end:-1:length(orig) - -1])
for i in 1:length(orig) - 1
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == [])
@test_throws StopIteration next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
a[begin:end] = data
@test (collect(it) == [])
end
end

function test_step_overflow(self::ListTest)
a = [0, 1, 2, 3, 4]
a[end:sys.maxsize:2] = [0]
@test (a[end:sys.maxsize:4] == [3])
end

function test_no_comdat_folding(self::L)
mutable struct L <: AbstractL

end

assertRaises(self, TypeError) do 
(3,) + L([1, 2])
end
end

function test_equal_operator_modifying_operand(self::Z)
mutable struct X <: AbstractX

end
function __eq__(self::X, other)
clear(list2)
return NotImplemented
end

mutable struct Y <: AbstractY

end
function __eq__(self::Y, other)
clear(list1)
return NotImplemented
end

mutable struct Z <: AbstractZ

end
function __eq__(self::Z, other)
clear(list3)
return NotImplemented
end

list1 = [X()]
list2 = [Y()]
assertTrue(self, list1 == list2)
list3 = [Z()]
list4 = [1]
assertFalse(self, list3 == list4)
end

function test_preallocation(self::ListTest)
iterable = repeat([0],10)
iter_size = getsizeof(sys, iterable)
@test (iter_size == getsizeof(sys, collect(repeat([0],10))))
@test (iter_size == getsizeof(sys, collect(0:9)))
end

function test_count_index_remove_crashes(self::L)
mutable struct X <: AbstractX

end
function __eq__(self::X, other)
clear(lst)
return NotImplemented
end

lst = [X()]
assertRaises(self, ValueError) do 
findfirst(isequal(lst), lst)
end
mutable struct L <: AbstractL

end
function __eq__(self::L, other)
string(other)
return NotImplemented
end

lst = L([X()])
count(isequal(lst), lst)
lst = L([X()])
assertRaises(self, ValueError) do 
deleteat!(lst, findfirst(isequal(lst), lst))
end
lst = [X(), X()]
3 ∈ lst
lst = [X(), X()]
X() ∈ lst
end

function main()

end

main()