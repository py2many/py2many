using Test







abstract type AbstractMyIndexable <: Abstractobject end
abstract type AbstractSliceTest end
abstract type AbstractExc <: AbstractException end
abstract type AbstractBadCmp <: Abstractobject end
abstract type AbstractAnyClass end
abstract type AbstractX <: Abstractobject end
abstract type Abstractmyobj end
function evaluate_slice_index(arg)
#= 
    Helper function to convert a slice argument to an integer, and raise
    TypeError with a suitable message on failure.

     =#
if hasattr(arg, "__index__")
return index(operator, arg)
else
throw(TypeError("slice indices must be integers or None or have an __index__ method"))
end
end

function slice_indices(slice, length)::Tuple
#= 
    Reference implementation for the slice.indices method.

     =#
length = index(operator, length)
step = slice.step === nothing ? (1) : (evaluate_slice_index(slice.step))
if length < 0
throw(ValueError("length should not be negative"))
end
if step == 0
throw(ValueError("slice step cannot be zero"))
end
lower = step < 0 ? (-1) : (0)
upper = step < 0 ? (length - 1) : (length)
if slice.start === nothing
start = step < 0 ? (upper) : (lower)
else
start = evaluate_slice_index(slice.start)
start = start < 0 ? (max(start + length, lower)) : (min(start, upper))
end
if slice.stop === nothing
stop = step < 0 ? (lower) : (upper)
else
stop = evaluate_slice_index(slice.stop)
stop = stop < 0 ? (max(stop + length, lower)) : (min(stop, upper))
end
return (start, stop, step)
end

mutable struct MyIndexable <: AbstractMyIndexable
value
end
function __index__(self::MyIndexable)
return self.value
end

mutable struct SliceTest <: AbstractSliceTest

end
function test_constructor(self::SliceTest)
@test_throws TypeError slice()
@test_throws TypeError slice(1, 2, 3, 4)
end

function test_repr(self::SliceTest)
@test (repr((1:2)) == "slice(1, 2, 3)")
end

function test_hash(self::SliceTest)
@test_throws TypeError hash(slice(5))
assertRaises(self, TypeError) do 
__hash__(slice(5))
end
end

function test_cmp(self::BadCmp)
s1 = (1:2)
s2 = (1:2)
s3 = (1:2)
assertEqual(self, s1, s2)
assertNotEqual(self, s1, s3)
assertNotEqual(self, s1, nothing)
assertNotEqual(self, s1, (1, 2, 3))
assertNotEqual(self, s1, "")
mutable struct Exc <: AbstractExc

end

mutable struct BadCmp <: AbstractBadCmp

end
function __eq__(self::BadCmp, other)
throw(Exc)
end

s1 = slice(BadCmp())
s2 = slice(BadCmp())
assertEqual(self, s1, s1)
assertRaises(self, Exc, () -> s1 === s2)
s1 = (1:BadCmp())
s2 = (1:BadCmp())
assertEqual(self, s1, s1)
assertRaises(self, Exc, () -> s1 === s2)
s1 = (1:2)
s2 = (1:2)
assertEqual(self, s1, s1)
assertRaises(self, Exc, () -> s1 === s2)
end

function test_members(self::AnyClass)
s = slice(1)
assertEqual(self, s.start, nothing)
assertEqual(self, s.stop, 1)
assertEqual(self, s.step, nothing)
s = (1:2)
assertEqual(self, s.start, 1)
assertEqual(self, s.stop, 2)
assertEqual(self, s.step, nothing)
s = (1:2)
assertEqual(self, s.start, 1)
assertEqual(self, s.stop, 2)
assertEqual(self, s.step, 3)
mutable struct AnyClass <: AbstractAnyClass

end

obj = AnyClass()
s = slice(obj)
assertTrue(self, s.stop == obj)
end

function check_indices(self::SliceTest, slice, length)
try
actual = indices(slice, length)
catch exn
if exn isa ValueError
actual = "valueerror"
end
end
try
expected = slice_indices(slice, length)
catch exn
if exn isa ValueError
expected = "valueerror"
end
end
@test (actual == expected)
if length >= 0 && slice.step != 0
actual = 0:indices(slice, length)... - 1
expected = 0:length - 1[slice + 1]
@test (actual == expected)
end
end

function test_indices(self::SliceTest)
@test (indices(slice(nothing), 10) == (0, 10, 1))
@test (indices((nothing:nothing), 10) == (0, 10, 2))
@test (indices((1:nothing), 10) == (1, 10, 2))
@test (indices((nothing:nothing), 10) == (9, -1, -1))
@test (indices((nothing:nothing), 10) == (9, -1, -2))
@test (indices((3:nothing), 10) == (3, -1, -2))
@test (indices((nothing:-9), 10) == (0, 1, 1))
@test (indices((nothing:-10), 10) == (0, 0, 1))
@test (indices((nothing:-11), 10) == (0, 0, 1))
@test (indices((nothing:-10), 10) == (9, 0, -1))
@test (indices((nothing:-11), 10) == (9, -1, -1))
@test (indices((nothing:-12), 10) == (9, -1, -1))
@test (indices((nothing:9), 10) == (0, 9, 1))
@test (indices((nothing:10), 10) == (0, 10, 1))
@test (indices((nothing:11), 10) == (0, 10, 1))
@test (indices((nothing:8), 10) == (9, 8, -1))
@test (indices((nothing:9), 10) == (9, 9, -1))
@test (indices((nothing:10), 10) == (9, 9, -1))
@test (indices((-100:100), 10) == indices(slice(nothing), 10))
@test (indices((100:-100), 10) == indices((nothing:nothing), 10))
@test (indices((-100:100), 10) == (0, 10, 2))
@test (collect(0:9)[end:sys.maxsize - 1:begin] == [0])
vals = [nothing, -(2^100), -(2^30), -53, -7, -1, 0, 1, 7, 53, 2^30, 2^100]
lengths = [0, 1, 7, 53, 2^30, 2^100]
for slice_args in product(itertools, vals, 3)
s = slice(slice_args...)
for length in lengths
check_indices(self, s, length)
end
end
check_indices(self, (0:10), -3)
assertRaises(self, ValueError) do 
indices(slice(nothing), -1)
end
assertRaises(self, ValueError) do 
indices((0:10), 5)
end
assertRaises(self, TypeError) do 
indices((0.0:10), 5)
end
assertRaises(self, TypeError) do 
indices((0:10.0), 5)
end
assertRaises(self, TypeError) do 
indices((0:10), 5)
end
assertRaises(self, TypeError) do 
indices((0:10), 5.0)
end
@test (indices((0:10), 5) == (0, 5, 1))
@test (indices((MyIndexable(0):10), 5) == (0, 5, 1))
@test (indices((0:MyIndexable(10)), 5) == (0, 5, 1))
@test (indices((0:10), 5) == (0, 5, 1))
@test (indices((0:10), MyIndexable(5)) == (0, 5, 1))
end

function test_setslice_without_getslice(self::X)
tmp = []
mutable struct X <: AbstractX

end
function __setitem__(self::X, i, k)
push!(tmp, (i, k))
end

x = X()
x[2:2] = 42
assertEqual(self, tmp, [((1:2), 42)])
end

function test_pickle(self::SliceTest)
s = (10:20)
for protocol in (0, 1, 2)
t = loads(dumps(s, protocol))
@test (s == t)
@test (indices(s, 15) == indices(t, 15))
assertNotEqual(self, id(s), id(t))
end
end

function test_cycle(self::myobj)
mutable struct myobj <: Abstractmyobj

end

o = myobj()
o.s = slice(o)
w = ref(weakref, o)
o = nothing
gc_collect(support)
assertIsNone(self, w())
end

function main()
slice_test = SliceTest()
test_constructor(slice_test)
test_repr(slice_test)
test_hash(slice_test)
test_cmp(slice_test)
test_members(slice_test)
check_indices(slice_test)
test_indices(slice_test)
test_setslice_without_getslice(slice_test)
test_pickle(slice_test)
test_cycle(slice_test)
end

main()