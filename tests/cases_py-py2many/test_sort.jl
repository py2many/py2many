using Test

import random

using functools: cmp_to_key
abstract type AbstractTestBase end
abstract type AbstractComplains <: Abstractobject end
abstract type AbstractStable <: Abstractobject end
abstract type AbstractTestBugs end
abstract type AbstractC end
abstract type AbstractTestDecorateSortUndecorate end
abstract type AbstractSortKiller <: Abstractobject end
abstract type AbstractTestOptimizedCompares end
abstract type AbstractWackyComparator <: Abstractint end
abstract type AbstractWackyList1 <: Abstractlist end
abstract type AbstractWackyList2 <: Abstractlist end
abstract type AbstractPointlessComparator end
verbose = support.verbose
nerrors = 0
function check(tag, expected, raw, compare = nothing)
global nerrors
if verbose
println("    checking", tag)
end
orig = raw[begin:end]
if compare
sort(raw, cmp_to_key(compare))
else
sort(raw)
end
if length(expected) != length(raw)
println("error in", tag)
println("length mismatch;", length(expected), length(raw))
println(expected)
println(orig)
println(raw)
nerrors += 1
return
end
for (i, good) in enumerate(expected)
maybe = raw[i + 1]
if good != maybe
println("error in", tag)
println("out of order at index", i, good, maybe)
println(expected)
println(orig)
println(raw)
nerrors += 1
return
end
end
end

mutable struct TestBase <: AbstractTestBase
i
index
key
maybe_complain::Bool

                    TestBase(i, index, key, maybe_complain::Bool = true) =
                        new(i, index, key, maybe_complain)
end
function testStressfully(self::Stable)
sizes = [0]
for power in 1:9
n = 2^power
append!(sizes, n - 1:n + 1)
end
append!(sizes, [10, 100, 1000])
mutable struct Complains <: AbstractComplains
i
maybe_complain::Bool

                    Complains(i, maybe_complain::Bool = true) =
                        new(i, maybe_complain)
end
function __lt__(self::Complains, other)::Bool
if Complains.maybe_complain && pylib::random::random() < 0.001
if verbose
println("        complaining at", self, other)
end
throw(RuntimeError)
end
return self.i < other.i
end

function __repr__(self::Complains)::String
return "Complains(%d)" % self.i
end

mutable struct Stable <: AbstractStable
key
index
end
function __lt__(self::Stable, other)::Bool
return self.key < other.key
end

function __repr__(self::Stable)
return "Stable(%d, %d)" % (self.key, self.index)
end

for n in sizes
x = collect(0:n - 1)
if verbose
println("Testing size", n)
end
s = x[begin:end]
check("identity", x, s)
s = x[begin:end]
reverse(s)
check("reversed", x, s)
s = x[begin:end]
shuffle(random, s)
check("random permutation", x, s)
y = x[begin:end]
reverse(y)
s = x[begin:end]
check("reversed via function", y, s, (a, b) -> b > a - b < a)
if verbose
println("    Checking against an insane comparison function.")
println("        If the implementation isn\'t careful, this may segfault.")
end
s = x[begin:end]
sort(s, cmp_to_key((a, b) -> Int(pylib::random::random()*3) - 1))
check("an insane function left some permutation", x, s)
if length(x) >= 2
function bad_key(x)
throw(RuntimeError)
end

s = x[begin:end]
assertRaises(self, RuntimeError, s.sort, bad_key)
end
x = [Complains(i) for i in x]
s = x[begin:end]
shuffle(random, s)
Complains.maybe_complain = true
it_complained = false
try
sort(s)
catch exn
if exn isa RuntimeError
it_complained = true
end
end
if it_complained
Complains.maybe_complain = false
check("exception during sort left some permutation", x, s)
end
s = [Stable(randrange(random, 10), i) for i in 0:n - 1]
augmented = [(e, e.index) for e in s]
sort(augmented)
x = [e for (e, i) in augmented]
check("stability", x, s)
end
end

mutable struct TestBugs <: AbstractTestBugs

end
function test_bug453523(self::C)
mutable struct C <: AbstractC

end
function __lt__(self::C, other)::Bool
if L && pylib::random::random() < 0.75
pop(L)
else
append(L, 3)
end
return pylib::random::random() < 0.5
end

L = [C() for i in 0:49]
assertRaises(self, ValueError, L.sort)
end

function test_undetected_mutation(self::TestBugs)
memorywaster = []
for i in 0:19
function mutating_cmp(x, y)::Bool
push!(L, 3)
pop(L)
return x > y - x < y
end

L = [1, 2]
@test_throws ValueError L.sort(cmp_to_key(mutating_cmp))
function mutating_cmp(x, y)::Bool
push!(L, 3)
#Delete Unsupported
del(L)
return x > y - x < y
end

@test_throws ValueError L.sort(cmp_to_key(mutating_cmp))
memorywaster = [memorywaster]
end
end

mutable struct TestDecorateSortUndecorate <: AbstractTestDecorateSortUndecorate

end
function test_decorated(self::TestDecorateSortUndecorate)
data = split("The quick Brown fox Jumped over The lazy Dog")
copy = data[begin:end]
shuffle(random, data)
sort(data, str.lower)
function my_cmp(x, y)::Bool
xlower, ylower = (lower(x), lower(y))
return xlower > ylower - xlower < ylower
end

sort(copy, cmp_to_key(my_cmp))
end

function test_baddecorator(self::TestDecorateSortUndecorate)
data = split("The quick Brown fox Jumped over The lazy Dog")
@test_throws TypeError data.sort((x, y) -> 0)
end

function test_stability(self::TestDecorateSortUndecorate)
data = [(randrange(random, 100), i) for i in 0:199]
copy = data[begin:end]
sort(data, (t) -> t[1])
sort(copy)
@test (data == copy)
end

function test_key_with_exception(self::TestDecorateSortUndecorate)
data = collect(-2:1)
dup = data[begin:end]
@test_throws ZeroDivisionError data.sort((x) -> 1 / x)
@test (data == dup)
end

function test_key_with_mutation(self::TestDecorateSortUndecorate)
data = collect(0:9)
function k(x)
#Delete Unsupported
del(data)
data[begin:end] = 0:19
return x
end

@test_throws ValueError data.sort(k)
end

function test_key_with_mutating_del(self::SortKiller)
data = collect(0:9)
mutable struct SortKiller <: AbstractSortKiller


            SortKiller(x) = begin
                #= pass =#
                new(x)
            end
end
function __del__(self::SortKiller)
#Delete Unsupported
del(data)
data[begin:end] = 0:19
end

function __lt__(self::SortKiller, other)::Bool
return id(self) < id(other)
end

assertRaises(self, ValueError, data.sort, SortKiller)
end

function test_key_with_mutating_del_and_exception(self::SortKiller)
data = collect(0:9)
mutable struct SortKiller <: AbstractSortKiller


            SortKiller(x) = begin
                if x > 2
throw(RuntimeError)
end
                new(x)
            end
end
function __del__(self::SortKiller)
#Delete Unsupported
del(data)
data[begin:end] = collect(0:19)
end

assertRaises(self, RuntimeError, data.sort, SortKiller)
end

function test_reverse(self::TestDecorateSortUndecorate)
data = collect(0:99)
shuffle(random, data)
sort(data, true)
@test (data == collect(0:-1:99))
end

function test_reverse_stability(self::TestDecorateSortUndecorate)
data = [(randrange(random, 100), i) for i in 0:199]
copy1 = data[begin:end]
copy2 = data[begin:end]
function my_cmp(x, y)::Bool
x0, y0 = (x[1], y[1])
return x0 > y0 - x0 < y0
end

function my_cmp_reversed(x, y)::Bool
x0, y0 = (x[1], y[1])
return y0 > x0 - y0 < x0
end

sort(data, cmp_to_key(my_cmp), true)
sort(copy1, cmp_to_key(my_cmp_reversed))
@test (data == copy1)
sort(copy2, (x) -> x[1], true)
@test (data == copy2)
end

function check_against_PyObject_RichCompareBool(self::TestOptimizedCompares, L)
pylib::random::reseed_from_f64(0)
shuffle(random, L)
L_1 = L[begin:end]
L_2 = [(x,) for x in L]
L_3 = [((x,),) for x in L]
for L in [L_1, L_2, L_3]
optimized = sorted(L)
reference = [y[2] for y in sorted([(0, x) for x in L])]
for (opt, ref) in zip(optimized, reference)
assertIs(self, opt, ref)
end
end
end

mutable struct TestOptimizedCompares <: AbstractTestOptimizedCompares

end
function test_safe_object_compare(self::TestOptimizedCompares)
heterogeneous_lists = [[0, "foo"], [0.0, "foo"], [("foo",), "foo"]]
for L in heterogeneous_lists
@test_throws TypeError L.sort()
@test_throws TypeError [(x,) for x in L].sort()
@test_throws TypeError [((x,),) for x in L].sort()
end
float_int_lists = [[1, 1.1], [1 << 70, 1.1], [1.1, 1], [1.1, 1 << 70]]
for L in float_int_lists
check_against_PyObject_RichCompareBool(self, L)
end
end

function test_unsafe_object_compare(self::PointlessComparator)
mutable struct WackyComparator <: AbstractWackyComparator

end
function __lt__(self::WackyComparator, other)
elem.__class__ = WackyList2
return __lt__(int, self)
end

mutable struct WackyList1 <: AbstractWackyList1

end

mutable struct WackyList2 <: AbstractWackyList2

end
function __lt__(self::WackyList2, other)
throw(ValueError)
end

L = [WackyList1([WackyComparator(i), i]) for i in 0:9]
elem = L[end]
assertRaises(self, ValueError) do 
sort(L)
end
L = [WackyList1([WackyComparator(i), i]) for i in 0:9]
elem = L[end]
assertRaises(self, ValueError) do 
sort([(x,) for x in L])
end
mutable struct PointlessComparator <: AbstractPointlessComparator

end
function __lt__(self::PointlessComparator, other)
return NotImplemented
end

L = [PointlessComparator(), PointlessComparator()]
assertRaises(self, TypeError, L.sort)
assertRaises(self, TypeError, [(x,) for x in L].sort)
lists = [append!(collect(0:99), [1 << 70]), [string(x) for x in 0:99] + ["￿"], [bytes(x) for x in 0:99], [cmp_to_key((x, y) -> x < y)(x) for x in 0:99]]
for L in lists
check_against_PyObject_RichCompareBool(self, L)
end
end

function test_unsafe_latin_compare(self::TestOptimizedCompares)
check_against_PyObject_RichCompareBool(self, [string(x) for x in 0:99])
end

function test_unsafe_long_compare(self::TestOptimizedCompares)
check_against_PyObject_RichCompareBool(self, [x for x in 0:99])
end

function test_unsafe_float_compare(self::TestOptimizedCompares)
check_against_PyObject_RichCompareBool(self, [float(x) for x in 0:99])
end

function test_unsafe_tuple_compare(self::TestOptimizedCompares)
check_against_PyObject_RichCompareBool(self, repeat([float("nan")],100))
check_against_PyObject_RichCompareBool(self, [float("nan") for _ in 0:99])
end

function test_not_all_tuples(self::TestOptimizedCompares)
@test_throws TypeError [(1.0, 1.0), (false, "A"), 6].sort()
@test_throws TypeError [("a", 1), (1, "a")].sort()
@test_throws TypeError [(1, "a"), ("a", 1)].sort()
end

function main()
test_base = TestBase()
testStressfully(test_base)
test_bugs = TestBugs()
test_bug453523(test_bugs)
test_undetected_mutation(test_bugs)
test_decorate_sort_undecorate = TestDecorateSortUndecorate()
test_decorated(test_decorate_sort_undecorate)
test_baddecorator(test_decorate_sort_undecorate)
test_stability(test_decorate_sort_undecorate)
test_key_with_exception(test_decorate_sort_undecorate)
test_key_with_mutation(test_decorate_sort_undecorate)
test_key_with_mutating_del(test_decorate_sort_undecorate)
test_key_with_mutating_del_and_exception(test_decorate_sort_undecorate)
test_reverse(test_decorate_sort_undecorate)
test_reverse_stability(test_decorate_sort_undecorate)
test_optimized_compares = TestOptimizedCompares()
test_safe_object_compare(test_optimized_compares)
test_unsafe_object_compare(test_optimized_compares)
test_unsafe_latin_compare(test_optimized_compares)
test_unsafe_long_compare(test_optimized_compares)
test_unsafe_float_compare(test_optimized_compares)
test_unsafe_tuple_compare(test_optimized_compares)
test_not_all_tuples(test_optimized_compares)
end

main()