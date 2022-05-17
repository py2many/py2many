using Test





abstract type AbstractRangeTest end
abstract type AbstractBadExc <: AbstractException end
abstract type AbstractBadCmp end
abstract type AbstractI end
abstract type AbstractIX end
abstract type AbstractIN end
abstract type AbstractC2 end
abstract type AbstractC3 <: Abstractint end
function pyrange(start, stop, step)
Channel() do ch_pyrange 
if ((start - stop) ÷ step) < 0
stop += (start - stop) % step
while start != stop
put!(ch_pyrange, start)
start += step
end
end
end
end

function pyrange_reversed(start, stop, step)
stop += (start - stop) % step
return pyrange(stop - step, start - step, -(step))
end

mutable struct RangeTest <: AbstractRangeTest
n::Int64
end
function assert_iterators_equal(self::RangeTest, xs, ys, test_id, limit = nothing)
if limit != nothing
xs = (xs for _ in (0:limit))
ys = (ys for _ in (0:limit))
end
sentinel = object()
pairs = zip_longest(itertools, xs, ys, sentinel)
for (i, (x, y)) in enumerate(pairs)
if x == y
continue;
elseif x == sentinel
fail(self, "$(): iterator ended unexpectedly at position $(); expected $()")
elseif y == sentinel
fail(self, "$(): unexpected excess element $() at position $()")
else
fail(self, "$(): wrong element at position $(); expected $(), got $()")
end
end
end

function test_range(self::RangeTest)
@test (collect(0:2) == [0, 1, 2])
@test (collect(1:4) == [1, 2, 3, 4])
@test (collect(0:-1) == [])
@test (collect(0:-2) == [])
@test (collect(1:3:9) == [1, 4, 7])
@test (collect(-4:-3:5) == [5, 2, -1, -4])
a = 10
b = 100
c = 50
@test (collect(a:a + 1) == [a, a + 1])
@test (collect(a - 1:-1:a + 2) == [a + 2, a + 1])
@test (collect(a - 1:-2:a + 4) == [a + 4, a + 2])
seq = collect(a:c:b - 1)
assertIn(self, a, seq)
assertNotIn(self, b, seq)
@test (length(seq) == 2)
seq = collect(a - 1:-(c):b)
assertIn(self, b, seq)
assertNotIn(self, a, seq)
@test (length(seq) == 2)
seq = collect(-(b) - 1:-(c):-(a))
assertIn(self, -(a), seq)
assertNotIn(self, -(b), seq)
@test (length(seq) == 2)
@test_throws TypeError range()
@test_throws TypeError range(1, 2, 3, 4)
@test_throws ValueError range(1, 2, 0)
@test_throws TypeError range(0.0, 2, 1)
@test_throws TypeError range(1, 2.0, 1)
@test_throws TypeError range(1, 2, 1.0)
@test_throws TypeError range(1e+100, 1e+101, 1e+101)
@test_throws TypeError range(0, "spam")
@test_throws TypeError range(0, 42, "spam")
@test (length(0:sys.maxsize - 1:sys.maxsize - 1) == 2)
r = -(sys.maxsize):2:sys.maxsize - 1
@test (length(r) == sys.maxsize)
end

function test_range_constructor_error_messages(self::RangeTest)
assertRaisesRegex(self, TypeError, "range expected at least 1 argument, got 0") do 
range()
end
assertRaisesRegex(self, TypeError, "range expected at most 3 arguments, got 6") do 
1:1
end
end

function test_large_operands(self::RangeTest)
x = 10^20:3:10^20
@test (length(x) == 4)
@test (length(collect(x)) == 4)
x = 10^20:3:10^20
@test (length(x) == 0)
@test (length(collect(x)) == 0)
@test !(x)
x = 10^20:-3:10^20
@test (length(x) == 0)
@test (length(collect(x)) == 0)
@test !(x)
x = 10^20:-3:10^20
@test (length(x) == 4)
@test (length(collect(x)) == 4)
@test x
for x in [0:-(2^100) - 1, 0:-(2^100) - 1, 2^100:-1:0]
@test (collect(x) == [])
@test !(x)
end
a = Int(10*sys.maxsize)
b = Int(100*sys.maxsize)
c = Int(50*sys.maxsize)
@test (collect(a:a + 1) == [a, a + 1])
@test (collect(a - 1:-1:a + 2) == [a + 2, a + 1])
@test (collect(a - 1:-2:a + 4) == [a + 4, a + 2])
seq = collect(a:c:b - 1)
assertIn(self, a, seq)
assertNotIn(self, b, seq)
@test (length(seq) == 2)
@test (seq[1] == a)
@test (seq[end] == a + c)
seq = collect(a - 1:-(c):b)
assertIn(self, b, seq)
assertNotIn(self, a, seq)
@test (length(seq) == 2)
@test (seq[1] == b)
@test (seq[end] == b - c)
seq = collect(-(b) - 1:-(c):-(a))
assertIn(self, -(a), seq)
assertNotIn(self, -(b), seq)
@test (length(seq) == 2)
@test (seq[1] == -(a))
@test (seq[end] == -(a) - c)
end

function test_large_range(self::RangeTest)
function _range_len(x)::Int64
try
length = length(x)
catch exn
if exn isa OverflowError
step = x[2] - x[1]
length = 1 + ((x[end] - x[1]) ÷ step)
end
end
return length
end

a = -(sys.maxsize)
b = sys.maxsize
expected_len = b - a
x = a:b - 1
assertIn(self, a, x)
assertNotIn(self, b, x)
@test_throws OverflowError len(x)
@test x
@test (_range_len(x) == expected_len)
@test (x[1] == a)
idx = sys.maxsize + 1
@test (x[idx + 1] == a + idx)
@test (x[idx + 1:idx + 1][1] == a + idx)
assertRaises(self, IndexError) do 
x[-(expected_len)]
end
assertRaises(self, IndexError) do 
x[expected_len + 1]
end
a = 0
b = 2*sys.maxsize
expected_len = b - a
x = a:b - 1
assertIn(self, a, x)
assertNotIn(self, b, x)
@test_throws OverflowError len(x)
@test x
@test (_range_len(x) == expected_len)
@test (x[1] == a)
idx = sys.maxsize + 1
@test (x[idx + 1] == a + idx)
@test (x[idx + 1:idx + 1][1] == a + idx)
assertRaises(self, IndexError) do 
x[-(expected_len)]
end
assertRaises(self, IndexError) do 
x[expected_len + 1]
end
a = 0
b = sys.maxsize^10
c = 2*sys.maxsize
expected_len = 1 + ((b - a) ÷ c)
x = a:c:b - 1
assertIn(self, a, x)
assertNotIn(self, b, x)
@test_throws OverflowError len(x)
@test x
@test (_range_len(x) == expected_len)
@test (x[1] == a)
idx = sys.maxsize + 1
@test (x[idx + 1] == a + idx*c)
@test (x[idx + 1:idx + 1][1] == a + idx*c)
assertRaises(self, IndexError) do 
x[-(expected_len)]
end
assertRaises(self, IndexError) do 
x[expected_len + 1]
end
a = sys.maxsize^10
b = 0
c = -2*sys.maxsize
expected_len = 1 + ((b - a) ÷ c)
x = a:c:b - 1
assertIn(self, a, x)
assertNotIn(self, b, x)
@test_throws OverflowError len(x)
@test x
@test (_range_len(x) == expected_len)
@test (x[1] == a)
idx = sys.maxsize + 1
@test (x[idx + 1] == a + idx*c)
@test (x[idx + 1:idx + 1][1] == a + idx*c)
assertRaises(self, IndexError) do 
x[-(expected_len)]
end
assertRaises(self, IndexError) do 
x[expected_len + 1]
end
end

function test_invalid_invocation(self::RangeTest)
@test_throws TypeError range()
@test_throws TypeError range(1, 2, 3, 4)
@test_throws ValueError range(1, 2, 0)
a = Int(10*sys.maxsize)
@test_throws ValueError range(a, a + 1, Int(0))
@test_throws TypeError range(1.0, 1.0, 1.0)
@test_throws TypeError range(1e+100, 1e+101, 1e+101)
@test_throws TypeError range(0, "spam")
@test_throws TypeError range(0, 42, "spam")
@test_throws TypeError range(0.0)
@test_throws TypeError range(0, 0.0)
@test_throws TypeError range(0.0, 0)
@test_throws TypeError range(0.0, 0.0)
@test_throws TypeError range(0, 0, 1.0)
@test_throws TypeError range(0, 0.0, 1)
@test_throws TypeError range(0, 0.0, 1.0)
@test_throws TypeError range(0.0, 0, 1)
@test_throws TypeError range(0.0, 0, 1.0)
@test_throws TypeError range(0.0, 0.0, 1)
@test_throws TypeError range(0.0, 0.0, 1.0)
end

function test_index(self::BadCmp)
u = 0:1
assertEqual(self, index(u, 0), 0)
assertEqual(self, index(u, 1), 1)
assertRaises(self, ValueError, u.index, 2)
u = -2:2
assertEqual(self, count(u, 0), 1)
assertEqual(self, index(u, 0), 2)
assertRaises(self, TypeError, u.index)
mutable struct BadExc <: AbstractBadExc

end

mutable struct BadCmp <: AbstractBadCmp

end
function __eq__(self::BadCmp, other)::Bool
if other == 2
throw(BadExc())
end
return false
end

a = 0:3
assertRaises(self, BadExc, a.index, BadCmp())
a = -2:2
assertEqual(self, index(a, 0), 2)
assertEqual(self, index(1:3:9, 4), 1)
assertEqual(self, index(-9:-3:1, -5), 2)
assertEqual(self, index(0:10^20, 1), 1)
assertEqual(self, index(0:10^20, 10^20 - 1), 10^20 - 1)
assertRaises(self, ValueError, 1:2:2^100.index, 2^87)
assertEqual(self, index(1:2:2^100, 2^87 + 1), 2^86)
assertEqual(self, index(0:9, ALWAYS_EQ), 0)
end

function test_user_index_method(self::IN)
bignum = 2*sys.maxsize
smallnum = 42
mutable struct I <: AbstractI
n::Int64
end
function __index__(self::I)::Int64
return self.n
end

assertEqual(self, collect(I(bignum):I(bignum + 1) - 1), [bignum])
assertEqual(self, collect(I(smallnum):I(smallnum + 1) - 1), [smallnum])
mutable struct IX <: AbstractIX

end
function __index__(self::IX)
throw(RuntimeError)
end

assertRaises(self, RuntimeError, range, IX())
mutable struct IN <: AbstractIN

end
function __index__(self::IN)::String
return "not a number"
end

assertRaises(self, TypeError, range, IN())
assertEqual(self, 0:9[begin:I(5)], 0:4)
assertRaises(self, RuntimeError) do 
0:9[begin:IX()]
end
assertRaises(self, TypeError) do 
0:9[begin:IN()]
end
end

function test_count(self::RangeTest)
@test (count(0:2, -1) == 0)
@test (count(0:2, 0) == 1)
@test (count(0:2, 1) == 1)
@test (count(0:2, 2) == 1)
@test (count(0:2, 3) == 0)
assertIs(self, type_(count(0:2, -1)), int)
assertIs(self, type_(count(0:2, 1)), int)
@test (count(0:10^20, 1) == 1)
@test (count(0:10^20, 10^20) == 0)
@test (index(0:2, 1) == 1)
@test (count(1:2:2^100, 2^87) == 0)
@test (count(1:2:2^100, 2^87 + 1) == 1)
@test (count(0:9, ALWAYS_EQ) == 10)
@test (length(sys.maxsize:sys.maxsize + 9) == 10)
end

function test_repr(self::RangeTest)
@test (repr(0:0) == "range(0, 1)")
@test (repr(1:1) == "range(1, 2)")
@test (repr(1:3:1) == "range(1, 2, 3)")
end

function test_pickling(self::RangeTest)
testcases = [(13,), (0, 11), (-22, 10), (20, 3, -1), (13, 21, 3), (-2, 2, 2), (2^65, 2^65 + 2)]
for proto in 0:pickle.HIGHEST_PROTOCOL
for t in testcases
subTest(self, proto, t) do 
r = 0:t... - 1
@test (collect(loads(pickle, dumps(pickle, r, proto))) == collect(r))
end
end
end
end

function test_iterator_pickling(self::RangeTest)
testcases = [(13,), (0, 11), (-22, 10), (20, 3, -1), (13, 21, 3), (-2, 2, 2)]
for M in (2^31, 2^63)
testcases = append!(testcases, [(M - 3, M - 1), (4*M, 4*M + 2), (M - 2, M - 1, 2), (-(M) + 1, -(M), -2), (1, 2, M - 1), (-1, -2, -(M)), (1, M - 1, M - 1), (-1, -(M), -(M))])
end
for proto in 0:pickle.HIGHEST_PROTOCOL
for t in testcases
subTest(self, proto, t) do 
it = (x for x in 0:t... - 1)
itorg = (x for x in 0:t... - 1)
data = collect(0:t... - 1)
d = dumps(pickle, it, proto)
it = loads(pickle, d)
@test (type_(itorg) == type_(it))
@test (collect(it) == data)
it = loads(pickle, d)
try
next(it)
catch exn
if exn isa StopIteration
continue;
end
end
d = dumps(pickle, it, proto)
it = loads(pickle, d)
@test (collect(it) == data[2:end])
end
end
end
end

function test_iterator_pickling_overflowing_index(self::RangeTest)
for proto in 0:pickle.HIGHEST_PROTOCOL
subTest(self, proto) do 
it = (x for x in 0:2^32)
_, _, idx = __reduce__(it)
@test (idx == 0)
__setstate__(it, 2^32 + 1)
_, _, idx = __reduce__(it)
@test (idx == 2^32 + 1)
d = dumps(pickle, it, proto)
it = loads(pickle, d)
@test (next(it) == 2^32 + 1)
end
end
end

function test_exhausted_iterator_pickling(self::RangeTest)
for proto in 0:pickle.HIGHEST_PROTOCOL
r = 2^65:2^65
i = (x for x in r)
while true
r = next(i)
if r == (2^65 + 1)
break;
end
end
d = dumps(pickle, i, proto)
i2 = loads(pickle, d)
@test (collect(i) == [])
@test (collect(i2) == [])
end
end

function test_large_exhausted_iterator_pickling(self::RangeTest)
for proto in 0:pickle.HIGHEST_PROTOCOL
r = 0:19
i = (x for x in r)
while true
r = next(i)
if r == 19
break;
end
end
d = dumps(pickle, i, proto)
i2 = loads(pickle, d)
@test (collect(i) == [])
@test (collect(i2) == [])
end
end

function test_odd_bug(self::RangeTest)
assertRaises(self, TypeError) do 
0:-1:[]
end
end

function test_types(self::C3)
assertIn(self, 1.0, 0:2)
assertIn(self, true, 0:2)
assertIn(self, 1 + 0im, 0:2)
assertIn(self, ALWAYS_EQ, 0:2)
mutable struct C2 <: AbstractC2

end
function __int__(self::C2)::Int64
return 1
end

function __index__(self::C2)::Int64
return 1
end

assertNotIn(self, C2(), 0:2)
assertIn(self, parse(Int, C2()), 0:2)
mutable struct C3 <: AbstractC3

end
function __eq__(self::C3, other)::Bool
return true
end

assertIn(self, C3(11), 0:9)
assertIn(self, C3(11), collect(0:9))
end

function test_strided_limits(self::RangeTest)
r = 0:2:100
assertIn(self, 0, r)
assertNotIn(self, 1, r)
assertIn(self, 2, r)
assertNotIn(self, 99, r)
assertIn(self, 100, r)
assertNotIn(self, 101, r)
r = -19:-1:0
assertIn(self, 0, r)
assertIn(self, -1, r)
assertIn(self, -19, r)
assertNotIn(self, -20, r)
r = -19:-2:0
assertIn(self, -18, r)
assertNotIn(self, -19, r)
assertNotIn(self, -20, r)
end

function test_empty(self::RangeTest)
r = 0:-1
assertNotIn(self, 0, r)
assertNotIn(self, 1, r)
r = 0:-9
assertNotIn(self, 0, r)
assertNotIn(self, -1, r)
assertNotIn(self, 1, r)
end

function test_range_iterators(self::RangeTest)
limits = [base + jiggle for M in (2^32, 2^64) for base in (-(M), -(M) ÷ 2, 0, M ÷ 2, M) for jiggle in (-2, -1, 0, 1, 2)]
test_ranges = [(start, end_, step) for start in limits for end_ in limits for step in (-(2^63), -(2^31), -2, -1, 1, 2)]
for (start, end_, step) in test_ranges
iter1 = start:step:end_ - 1
iter2 = pyrange(start, end_, step)
test_id = "range($(), $(), $())"
assert_iterators_equal(self, iter1, iter2, test_id)
iter1 = reversed(start:step:end_ - 1)
iter2 = pyrange_reversed(start, end_, step)
test_id = "reversed(range($(), $(), $()))"
assert_iterators_equal(self, iter1, iter2, test_id)
end
end

function test_range_iterators_invocation(self::RangeTest)
rangeiter_type = type_((x for x in 0:-1))
@test_throws TypeError rangeiter_type(1, 3, 1)
long_rangeiter_type = type_((x for x in 0:1 << 1000))
@test_throws TypeError long_rangeiter_type(1, 3, 1)
end

function test_slice(self::RangeTest)
function check(start, stop, step = nothing)
i = (start:stop)
@test (collect(r[i + 1]) == collect(r)[i + 1])
@test (length(r[i + 1]) == length(collect(r)[i + 1]))
end

for r in [0:9, 0:-1, 1:3:8, -1:-3:8, sys.maxsize + 1:sys.maxsize + 9]
check(0, 2)
check(0, 20)
check(1, 2)
check(20, 30)
check(-30, -20)
check(-1, 100, 2)
check(0, -1)
check(-1, -3, -1)
end
end

function test_contains(self::RangeTest)
r = 0:9
assertIn(self, 0, r)
assertIn(self, 1, r)
assertIn(self, 5.0, r)
assertNotIn(self, 5.1, r)
assertNotIn(self, -1, r)
assertNotIn(self, 10, r)
assertNotIn(self, "", r)
r = 0:-1:9
assertIn(self, 0, r)
assertIn(self, 1, r)
assertIn(self, 5.0, r)
assertNotIn(self, 5.1, r)
assertNotIn(self, -1, r)
assertNotIn(self, 10, r)
assertNotIn(self, "", r)
r = 0:2:9
assertIn(self, 0, r)
assertNotIn(self, 1, r)
assertNotIn(self, 5.0, r)
assertNotIn(self, 5.1, r)
assertNotIn(self, -1, r)
assertNotIn(self, 10, r)
assertNotIn(self, "", r)
r = 0:-2:9
assertNotIn(self, 0, r)
assertIn(self, 1, r)
assertIn(self, 5.0, r)
assertNotIn(self, 5.1, r)
assertNotIn(self, -1, r)
assertNotIn(self, 10, r)
assertNotIn(self, "", r)
end

function test_reverse_iteration(self::RangeTest)
for r in [0:9, 0:-1, 1:3:8, -1:-3:8, sys.maxsize + 1:sys.maxsize + 9]
@test (collect(reversed(r)) == collect(r)[end:-1:begin])
end
end

function test_issue11845(self::RangeTest)
r = 0:indices((1:18), 20)... - 1
values = Set([nothing, 0, 1, -1, 2, -2, 5, -5, 19, -19, 20, -20, 21, -21, 30, -30, 99, -99])
for i in values
for j in values
for k in values - Set([0])
r[j:k:i + 1]
end
end
end
end

function test_comparison(self::RangeTest)
test_ranges = [0:-1, 0:0, 1:3:0, 0:0, 5:5, 5:2:5, 5:2:6, 0:1, 0:2:3, 0:2:4, 0:2:5]
test_tuples = collect(map(tuple, test_ranges))
ranges_eq = [a == b for a in test_ranges for b in test_ranges]
tuples_eq = [a == b for a in test_tuples for b in test_tuples]
@test (ranges_eq == tuples_eq)
ranges_ne = [a != b for a in test_ranges for b in test_ranges]
@test (ranges_ne == [!(x) for x in ranges_eq])
for a in test_ranges
for b in test_ranges
if a == b
@test (hash(a) == hash(b))
end
end
end
assertIs(self, 0:-1 == (), false)
assertIs(self, () == 0:-1, false)
assertIs(self, 0:1 == [0, 1], false)
@test (0:2:2^100 == 0:2:2^100)
@test (hash(0:2:2^100) == hash(0:2:2^100))
assertNotEqual(self, 0:2:2^100, 0:2:2^100)
@test (2^200:2^100:2^201 - 2^99 - 1 == 2^200:2^100:2^201)
@test (hash(2^200:2^100:2^201 - 2^99 - 1) == hash(2^200:2^100:2^201))
assertNotEqual(self, 2^200:2^100:2^201, 2^200:2^100:2^201)
assertRaises(self, TypeError) do 
0:-1 < 0:-1
end
assertRaises(self, TypeError) do 
0:-1 > 0:-1
end
assertRaises(self, TypeError) do 
0:-1 <= 0:-1
end
assertRaises(self, TypeError) do 
0:-1 >= 0:-1
end
end

function test_attributes(self::RangeTest)
assert_attrs(self, 0:-1, 0, 0, 1)
assert_attrs(self, 0:9, 0, 10, 1)
assert_attrs(self, 0:-9, 0, -10, 1)
assert_attrs(self, 0:1:9, 0, 10, 1)
assert_attrs(self, 0:3:9, 0, 10, 3)
assert_attrs(self, -1:-1:10, 10, 0, -1)
assert_attrs(self, -1:-3:10, 10, 0, -3)
assert_attrs(self, 0:0, 0, 1, 1)
assert_attrs(self, false:0, 0, 1, 1)
assert_attrs(self, false:true:0, 0, 1, 1)
end

function assert_attrs(self::RangeTest, rangeobj, start, stop, step)
@test (rangeobj.start == start)
@test (rangeobj.stop == stop)
@test (rangeobj.step == step)
assertIs(self, type_(rangeobj.start), int)
assertIs(self, type_(rangeobj.stop), int)
assertIs(self, type_(rangeobj.step), int)
assertRaises(self, AttributeError) do 
rangeobj.start = 0
end
assertRaises(self, AttributeError) do 
rangeobj.stop = 10
end
assertRaises(self, AttributeError) do 
rangeobj.step = 1
end
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(rangeobj.start)
end
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(rangeobj.stop)
end
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(rangeobj.step)
end
end

function main()
range_test = RangeTest()
assert_iterators_equal(range_test)
test_range(range_test)
test_range_constructor_error_messages(range_test)
test_large_operands(range_test)
test_large_range(range_test)
test_invalid_invocation(range_test)
test_index(range_test)
test_user_index_method(range_test)
test_count(range_test)
test_repr(range_test)
test_pickling(range_test)
test_iterator_pickling(range_test)
test_iterator_pickling_overflowing_index(range_test)
test_exhausted_iterator_pickling(range_test)
test_large_exhausted_iterator_pickling(range_test)
test_odd_bug(range_test)
test_types(range_test)
test_strided_limits(range_test)
test_empty(range_test)
test_range_iterators(range_test)
test_range_iterators_invocation(range_test)
test_slice(range_test)
test_contains(range_test)
test_reverse_iteration(range_test)
test_issue11845(range_test)
test_comparison(range_test)
test_attributes(range_test)
assert_attrs(range_test)
end

main()