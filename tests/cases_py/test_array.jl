using ResumableFunctions
using Test
#= Test the arraymodule.
   Roger E. Masse
 =#
# import collections.abc


# using test.support: os_helper
# using test.support: _2G


abstract type Abstractarray end
abstract type AbstractArraySubclass <: Abstractarray end
abstract type AbstractArraySubclassWithKwargs <: Abstractarray end
abstract type AbstractMiscTest end
abstract type AbstractArrayReconstructorTest end
abstract type AbstractBaseTest end
abstract type AbstractStringTest <: AbstractBaseTest end
abstract type AbstractUnicodeTest <: AbstractStringTest end
abstract type AbstractNumberTest <: AbstractBaseTest end
abstract type AbstractIntegerNumberTest <: AbstractNumberTest end
abstract type AbstractIntable end
abstract type AbstractSignedNumberTest <: AbstractIntegerNumberTest end
abstract type AbstractUnsignedNumberTest <: AbstractIntegerNumberTest end
abstract type AbstractByteTest <: AbstractSignedNumberTest end
abstract type AbstractUnsignedByteTest <: AbstractUnsignedNumberTest end
abstract type AbstractShortTest <: AbstractSignedNumberTest end
abstract type AbstractUnsignedShortTest <: AbstractUnsignedNumberTest end
abstract type AbstractIntTest <: AbstractSignedNumberTest end
abstract type AbstractUnsignedIntTest <: AbstractUnsignedNumberTest end
abstract type AbstractLongTest <: AbstractSignedNumberTest end
abstract type AbstractUnsignedLongTest <: AbstractUnsignedNumberTest end
abstract type AbstractLongLongTest <: AbstractSignedNumberTest end
abstract type AbstractUnsignedLongLongTest <: AbstractUnsignedNumberTest end
abstract type AbstractFPTest <: AbstractNumberTest end
abstract type AbstractFloatTest <: AbstractFPTest end
abstract type AbstractDoubleTest <: AbstractFPTest end
abstract type AbstractLargeArrayTest end
using array: _array_reconstructor
sizeof_wchar = itemsize(array(array, "u"))
mutable struct ArraySubclass <: AbstractArraySubclass

end

mutable struct ArraySubclassWithKwargs <: AbstractArraySubclassWithKwargs
newarg::Any

            ArraySubclassWithKwargs(typecode, newarg = nothing) = begin
                __init__(array(array))(self)
                new(typecode, newarg = nothing)
            end
end

typecodes = "ubBhHiIlLfdqQ"
mutable struct MiscTest <: AbstractMiscTest

end
function test_array_is_sequence(self::AbstractMiscTest)
assertIsInstance(self, array(array, "B"), MutableSequence(abc(collections)))
assertIsInstance(self, array(array, "B"), Reversible(abc(collections)))
end

function test_bad_constructor(self::AbstractMiscTest)
@test_throws TypeError array(array)()
@test_throws TypeError array(array)(42)
@test_throws TypeError array(array)("xx")
@test_throws ValueError array(array)("x")
end

function test_disallow_instantiation(self::AbstractMiscTest)
my_array = array(array, "I")
check_disallow_instantiation(support, self, type_(iter(my_array)), my_array)
end

function test_immutable(self::AbstractMiscTest)
assertRaises(self, TypeError) do 
foo(array(array)) = 1
end
end

function test_empty(self::AbstractMiscTest)
a = array(array, "B")
a[begin:end] = a
@test (length(a) == 0)
@test (length(a + a) == 0)
@test (length(a*3) == 0)
a += a
@test (length(a) == 0)
end

UNKNOWN_FORMAT = -1
UNSIGNED_INT8 = 0
SIGNED_INT8 = 1
UNSIGNED_INT16_LE = 2
UNSIGNED_INT16_BE = 3
SIGNED_INT16_LE = 4
SIGNED_INT16_BE = 5
UNSIGNED_INT32_LE = 6
UNSIGNED_INT32_BE = 7
SIGNED_INT32_LE = 8
SIGNED_INT32_BE = 9
UNSIGNED_INT64_LE = 10
UNSIGNED_INT64_BE = 11
SIGNED_INT64_LE = 12
SIGNED_INT64_BE = 13
IEEE_754_FLOAT_LE = 14
IEEE_754_FLOAT_BE = 15
IEEE_754_DOUBLE_LE = 16
IEEE_754_DOUBLE_BE = 17
UTF16_LE = 18
UTF16_BE = 19
UTF32_LE = 20
UTF32_BE = 21
mutable struct ArrayReconstructorTest <: AbstractArrayReconstructorTest

end
function test_error(self::AbstractArrayReconstructorTest)
@test_throws TypeError array_reconstructor("", "b", 0, b"")
@test_throws TypeError array_reconstructor(str, "b", 0, b"")
@test_throws TypeError array_reconstructor(array(array), "b", "", b"")
@test_throws TypeError array_reconstructor(array(array), "b", 0, "")
@test_throws ValueError array_reconstructor(array(array), "?", 0, b"")
@test_throws ValueError array_reconstructor(array(array), "b", UNKNOWN_FORMAT, b"")
@test_throws ValueError array_reconstructor(array(array), "b", 22, b"")
@test_throws ValueError array_reconstructor(array(array), "d", 16, b"a")
end

function test_numbers(self::AbstractArrayReconstructorTest)
testcases = ((["B", "H", "I", "L"], UNSIGNED_INT8, "=BBBB", [128, 127, 0, 255]), (["b", "h", "i", "l"], SIGNED_INT8, "=bbb", [-128, 127, 0]), (["H", "I", "L"], UNSIGNED_INT16_LE, "<HHHH", [32768, 32767, 0, 65535]), (["H", "I", "L"], UNSIGNED_INT16_BE, ">HHHH", [32768, 32767, 0, 65535]), (["h", "i", "l"], SIGNED_INT16_LE, "<hhh", [-32768, 32767, 0]), (["h", "i", "l"], SIGNED_INT16_BE, ">hhh", [-32768, 32767, 0]), (["I", "L"], UNSIGNED_INT32_LE, "<IIII", [1 << 31, (1 << 31) - 1, 0, (1 << 32) - 1]), (["I", "L"], UNSIGNED_INT32_BE, ">IIII", [1 << 31, (1 << 31) - 1, 0, (1 << 32) - 1]), (["i", "l"], SIGNED_INT32_LE, "<iii", [-1 << 31, (1 << 31) - 1, 0]), (["i", "l"], SIGNED_INT32_BE, ">iii", [-1 << 31, (1 << 31) - 1, 0]), (["L"], UNSIGNED_INT64_LE, "<QQQQ", [1 << 31, (1 << 31) - 1, 0, (1 << 32) - 1]), (["L"], UNSIGNED_INT64_BE, ">QQQQ", [1 << 31, (1 << 31) - 1, 0, (1 << 32) - 1]), (["l"], SIGNED_INT64_LE, "<qqq", [-1 << 31, (1 << 31) - 1, 0]), (["l"], SIGNED_INT64_BE, ">qqq", [-1 << 31, (1 << 31) - 1, 0]), (["L"], UNSIGNED_INT64_LE, "<QQQQ", [1 << 63, (1 << 63) - 1, 0, (1 << 64) - 1]), (["L"], UNSIGNED_INT64_BE, ">QQQQ", [1 << 63, (1 << 63) - 1, 0, (1 << 64) - 1]), (["l"], SIGNED_INT64_LE, "<qqq", [-1 << 63, (1 << 63) - 1, 0]), (["l"], SIGNED_INT64_BE, ">qqq", [-1 << 63, (1 << 63) - 1, 0]), (["f"], IEEE_754_FLOAT_LE, "<ffff", [16711938.0, float("inf"), float("-inf"), -0.0]), (["f"], IEEE_754_FLOAT_BE, ">ffff", [16711938.0, float("inf"), float("-inf"), -0.0]), (["d"], IEEE_754_DOUBLE_LE, "<dddd", [9006104071832581.0, float("inf"), float("-inf"), -0.0]), (["d"], IEEE_754_DOUBLE_BE, ">dddd", [9006104071832581.0, float("inf"), float("-inf"), -0.0]))
for testcase in testcases
valid_typecodes, mformat_code, struct_fmt, values = testcase
arraystr = pack(struct_, struct_fmt, values...)
for typecode in valid_typecodes
try
a = array(array, typecode, values)
catch exn
if exn isa OverflowError
continue;
end
end
b = array_reconstructor(array(array), typecode, mformat_code, arraystr)
@test (a == b)
end
end
end

function test_unicode(self::AbstractArrayReconstructorTest)
teststr = "Bonne Journée 𠌊𠍇"
testcases = ((UTF16_LE, "UTF-16-LE"), (UTF16_BE, "UTF-16-BE"), (UTF32_LE, "UTF-32-LE"), (UTF32_BE, "UTF-32-BE"))
for testcase in testcases
mformat_code, encoding = testcase
a = array(array, "u", teststr)
b = array_reconstructor(array(array), "u", mformat_code, encode(teststr, encoding))
@test (a == b)
end
end

mutable struct BaseTest <: AbstractBaseTest

end
function assertEntryEqual(self::AbstractBaseTest, entry1, entry2)
assertEqual(self, entry1, entry2)
end

function badtypecode(self::AbstractBaseTest)
return typecodes[(index(typecodes, self.typecode) + 1) % length(typecodes)]
end

function test_constructor(self::AbstractBaseTest)
a = array(array, self.typecode)
assertEqual(self, typecode(a), self.typecode)
assertGreaterEqual(self, itemsize(a), self.minitemsize)
assertRaises(self, TypeError, array(array), self.typecode, nothing)
end

function test_len(self::AbstractBaseTest)
a = array(array, self.typecode)
append(a, self.example[1])
assertEqual(self, length(a), 1)
a = array(array, self.typecode, self.example)
assertEqual(self, length(a), length(self.example))
end

function test_buffer_info(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, buffer_info(a), 42)
bi = buffer_info(a)
assertIsInstance(self, bi, tuple)
assertEqual(self, length(bi), 2)
assertIsInstance(self, bi[1], int)
assertIsInstance(self, bi[2], int)
assertEqual(self, bi[2], length(a))
end

function test_byteswap(self::AbstractBaseTest)
if self.typecode == "u"
example = "􀄀"
else
example = self.example
end
a = array(array, self.typecode, example)
assertRaises(self, TypeError, byteswap(a), 42)
if itemsize(a) in (1, 2, 4, 8)
b = array(array, self.typecode, example)
byteswap(b)
if itemsize(a) == 1
assertEqual(self, a, b)
else
assertNotEqual(self, a, b)
end
byteswap(b)
assertEqual(self, a, b)
end
end

function test_copy(self::AbstractBaseTest)
import copy
a = array(array, self.typecode, self.example)
b = copy(copy, a)
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
end

function test_deepcopy(self::AbstractBaseTest)
import copy
a = array(array, self.typecode, self.example)
b = deepcopy(copy, a)
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
end

function test_reduce_ex(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
for protocol in (0:2)
assertIs(self, __reduce_ex__(a, protocol)[1], array(array))
end
for protocol in (3:HIGHEST_PROTOCOL(pickle) + 1 - 1)
assertIs(self, __reduce_ex__(a, protocol)[1], array_reconstructor)
end
end

function test_pickle(self::AbstractBaseTest)
for protocol in (0:HIGHEST_PROTOCOL(pickle) + 1 - 1)
a = array(array, self.typecode, self.example)
b = loads(pickle, dumps(pickle, a, protocol))
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
a = ArraySubclass(self.typecode, self.example)
x(a) = 10
b = loads(pickle, dumps(pickle, a, protocol))
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
assertEqual(self, x(a), x(b))
assertEqual(self, type_(a), type_(b))
end
end

function test_pickle_for_empty_array(self::AbstractBaseTest)
for protocol in (0:HIGHEST_PROTOCOL(pickle) + 1 - 1)
a = array(array, self.typecode)
b = loads(pickle, dumps(pickle, a, protocol))
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
a = ArraySubclass(self.typecode)
x(a) = 10
b = loads(pickle, dumps(pickle, a, protocol))
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
assertEqual(self, x(a), x(b))
assertEqual(self, type_(a), type_(b))
end
end

function test_iterator_pickle(self::AbstractBaseTest)
orig = array(array, self.typecode, self.example)
data = collect(orig)
data2 = data[begin:end]
for proto in (0:HIGHEST_PROTOCOL(pickle) + 1 - 1)
itorig = iter(orig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
fromlist(a, data2)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), data + data2)
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
fromlist(a, data2)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), data[2:end] + data2)
for i in (1:length(data) - 1)
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
fromlist(a, data2)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), data2)
assertRaises(self, StopIteration, next, itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
fromlist(a, data2)
assertEqual(self, collect(it), [])
end
end

function test_exhausted_iterator(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertEqual(self, collect(a), collect(self.example))
exhit = iter(a)
empit = iter(a)
for x in exhit
next(empit)
end
append(a, self.outside)
assertEqual(self, collect(exhit), [])
assertEqual(self, collect(empit), [self.outside])
assertEqual(self, collect(a), collect(self.example) + [self.outside])
end

function test_reverse_iterator(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertEqual(self, collect(a), collect(self.example))
assertEqual(self, collect(reversed(a)), collect(iter(a))[begin:end])
end

function test_reverse_iterator_picking(self::AbstractBaseTest)
orig = array(array, self.typecode, self.example)
data = collect(orig)
data2 = [self.outside] + data
rev_data = data[(length(data) - 2 + 1):end] + [self.outside]
for proto in (0:HIGHEST_PROTOCOL(pickle) + 1 - 1)
itorig = reversed(orig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
insert(a, 0, self.outside)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), rev_data)
assertEqual(self, collect(a), data2)
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
insert(a, 0, self.outside)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), rev_data[2:end])
assertEqual(self, collect(a), data2)
for i in (1:length(data) - 1)
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
insert(a, 0, self.outside)
assertEqual(self, type_(it), type_(itorig))
assertEqual(self, collect(it), [])
assertEqual(self, collect(a), data2)
assertRaises(self, StopIteration, next, itorig)
d = dumps(pickle, (itorig, orig), proto)
it, a = loads(pickle, d)
insert(a, 0, self.outside)
assertEqual(self, collect(it), [])
assertEqual(self, collect(a), data2)
end
end

function test_exhausted_reverse_iterator(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertEqual(self, collect(a), collect(self.example))
exhit = reversed(a)
empit = reversed(a)
for x in exhit
next(empit)
end
insert(a, 0, self.outside)
assertEqual(self, collect(exhit), [])
assertEqual(self, collect(empit), [])
assertEqual(self, collect(a), [self.outside] + collect(self.example))
end

function test_insert(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
insert(a, 0, self.example[1])
assertEqual(self, length(a), 1 + length(self.example))
assertEqual(self, a[1], a[2])
assertRaises(self, TypeError, insert(a))
assertRaises(self, TypeError, insert(a), nothing)
assertRaises(self, TypeError, insert(a), 0, nothing)
a = array(array, self.typecode, self.example)
insert(a, -1, self.example[1])
assertEqual(self, a, array(array, self.typecode, (self.example[begin:-1] + self.example[begin:1]) + self.example[end:end]))
a = array(array, self.typecode, self.example)
insert(a, -1000, self.example[1])
assertEqual(self, a, array(array, self.typecode, self.example[begin:1] + self.example))
a = array(array, self.typecode, self.example)
insert(a, 1000, self.example[1])
assertEqual(self, a, array(array, self.typecode, self.example + self.example[begin:1]))
end

function test_tofromfile(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
assertRaises(self, TypeError, tofile(a))
unlink(os_helper, os_helper.TESTFN)
f = readline(os_helper.TESTFN)
try
tofile(a, f)
close(f)
b = array(array, self.typecode)
f = readline(os_helper.TESTFN)
assertRaises(self, TypeError, fromfile(b))
fromfile(b, f, length(self.example))
assertEqual(self, b, array(array, self.typecode, self.example))
assertNotEqual(self, a, b)
assertRaises(self, EOFError, fromfile(b), f, length(self.example) + 1)
assertEqual(self, a, b)
close(f)
finally
if !(closed(f))
close(f)
end
unlink(os_helper, os_helper.TESTFN)
end
end

function test_fromfile_ioerror(self::AbstractBaseTest)
a = array(array, self.typecode)
f = readline(os_helper.TESTFN)
try
assertRaises(self, OSError, fromfile(a), f, length(self.example))
finally
close(f)
unlink(os_helper, os_helper.TESTFN)
end
end

function test_filewrite(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
f = readline(os_helper.TESTFN)
try
write(f, a)
close(f)
b = array(array, self.typecode)
f = readline(os_helper.TESTFN)
fromfile(b, f, length(self.example))
assertEqual(self, b, array(array, self.typecode, self.example))
assertNotEqual(self, a, b)
fromfile(b, f, length(self.example))
assertEqual(self, a, b)
close(f)
finally
if !(closed(f))
close(f)
end
unlink(os_helper, os_helper.TESTFN)
end
end

function test_tofromlist(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
b = array(array, self.typecode)
assertRaises(self, TypeError, tolist(a), 42)
assertRaises(self, TypeError, fromlist(b))
assertRaises(self, TypeError, fromlist(b), 42)
assertRaises(self, TypeError, fromlist(b), [nothing])
fromlist(b, tolist(a))
assertEqual(self, a, b)
end

function test_tofrombytes(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
b = array(array, self.typecode)
assertRaises(self, TypeError, tobytes(a), 42)
assertRaises(self, TypeError, frombytes(b))
assertRaises(self, TypeError, frombytes(b), 42)
frombytes(b, tobytes(a))
c = array(array, self.typecode, Vector{UInt8}(join(tobytes(a), "")))
assertEqual(self, a, b)
assertEqual(self, a, c)
if itemsize(a) > 1
assertRaises(self, ValueError, frombytes(b), b"x")
end
end

function test_fromarray(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
b = array(array, self.typecode, a)
assertEqual(self, a, b)
end

function test_repr(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
assertEqual(self, a, eval(repr(a), Dict("array" => array(array))))
a = array(array, self.typecode)
assertEqual(self, repr(a), "array('%s')" % self.typecode)
end

function test_str(self::AbstractBaseTest)
a = array(array, self.typecode, 2*self.example)
string(a)
end

function test_cmp(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertIs(self, a == 42, false)
assertIs(self, a != 42, true)
assertIs(self, a == a, true)
assertIs(self, a != a, false)
assertIs(self, a < a, false)
assertIs(self, a <= a, true)
assertIs(self, a > a, false)
assertIs(self, a >= a, true)
al = array(array, self.typecode, self.smallerexample)
ab = array(array, self.typecode, self.biggerexample)
assertIs(self, a == (2*a), false)
assertIs(self, a != (2*a), true)
assertIs(self, a < (2*a), true)
assertIs(self, a <= (2*a), true)
assertIs(self, a > (2*a), false)
assertIs(self, a >= (2*a), false)
assertIs(self, a == al, false)
assertIs(self, a != al, true)
assertIs(self, a < al, false)
assertIs(self, a <= al, false)
assertIs(self, a > al, true)
assertIs(self, a >= al, true)
assertIs(self, a == ab, false)
assertIs(self, a != ab, true)
assertIs(self, a < ab, true)
assertIs(self, a <= ab, true)
assertIs(self, a > ab, false)
assertIs(self, a >= ab, false)
end

function test_add(self::AbstractBaseTest)
a = array(array, self.typecode, self.example) + array(array, self.typecode, self.example[begin:end])
assertEqual(self, a, array(array, self.typecode, self.example + self.example[begin:end]))
b = array(array, badtypecode(self))
assertRaises(self, TypeError, __add__(a), b)
assertRaises(self, TypeError, __add__(a), "bad")
end

function test_iadd(self::AbstractBaseTest)
a = array(array, self.typecode, self.example[begin:end])
b = a
a += array(array, self.typecode, 2*self.example)
assertIs(self, a, b)
assertEqual(self, a, array(array, self.typecode, self.example[begin:end] + 2*self.example))
a = array(array, self.typecode, self.example)
a += a
assertEqual(self, a, array(array, self.typecode, self.example + self.example))
b = array(array, badtypecode(self))
assertRaises(self, TypeError, __add__(a), b)
assertRaises(self, TypeError, __iadd__(a), "bad")
end

function test_mul(self::AbstractBaseTest)
a = 5*array(array, self.typecode, self.example)
assertEqual(self, a, array(array, self.typecode, 5*self.example))
a = array(array, self.typecode, self.example)*5
assertEqual(self, a, array(array, self.typecode, self.example*5))
a = 0*array(array, self.typecode, self.example)
assertEqual(self, a, array(array, self.typecode))
a = -1*array(array, self.typecode, self.example)
assertEqual(self, a, array(array, self.typecode))
a = 5*array(array, self.typecode, self.example[begin:1])
assertEqual(self, a, array(array, self.typecode, repeat([a[1]],5)))
assertRaises(self, TypeError, __mul__(a), "bad")
end

function test_imul(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
b = a
a *= 5
assertIs(self, a, b)
assertEqual(self, a, array(array, self.typecode, 5*self.example))
a *= 0
assertIs(self, a, b)
assertEqual(self, a, array(array, self.typecode))
a *= 1000
assertIs(self, a, b)
assertEqual(self, a, array(array, self.typecode))
a *= -1
assertIs(self, a, b)
assertEqual(self, a, array(array, self.typecode))
a = array(array, self.typecode, self.example)
a *= -1
assertEqual(self, a, array(array, self.typecode))
assertRaises(self, TypeError, __imul__(a), "bad")
end

function test_getitem(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertEntryEqual(self, a[1], self.example[1])
assertEntryEqual(self, a[1], self.example[1])
assertEntryEqual(self, a[end], self.example[end])
assertEntryEqual(self, a[end], self.example[end])
assertEntryEqual(self, a[length(self.example) - 1], self.example[end])
assertEntryEqual(self, a[-length(self.example)], self.example[1])
assertRaises(self, TypeError, __getitem__(a))
assertRaises(self, IndexError, __getitem__(a), length(self.example))
assertRaises(self, IndexError, __getitem__(a), -length(self.example) - 1)
end

function test_setitem(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
a[1] = a[end]
assertEntryEqual(self, a[1], a[end])
a = array(array, self.typecode, self.example)
a[1] = a[end]
assertEntryEqual(self, a[1], a[end])
a = array(array, self.typecode, self.example)
a[end] = a[1]
assertEntryEqual(self, a[1], a[end])
a = array(array, self.typecode, self.example)
a[end] = a[1]
assertEntryEqual(self, a[1], a[end])
a = array(array, self.typecode, self.example)
a[length(self.example) - 1] = a[1]
assertEntryEqual(self, a[1], a[end])
a = array(array, self.typecode, self.example)
a[-length(self.example)] = a[end]
assertEntryEqual(self, a[1], a[end])
assertRaises(self, TypeError, __setitem__(a))
assertRaises(self, TypeError, __setitem__(a), nothing)
assertRaises(self, TypeError, __setitem__(a), 0, nothing)
assertRaises(self, IndexError, __setitem__(a), length(self.example), self.example[1])
assertRaises(self, IndexError, __setitem__(a), -length(self.example) - 1, self.example[1])
end

function test_delitem(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
a[1]!
assertEqual(self, a, array(array, self.typecode, self.example[2:end]))
a = array(array, self.typecode, self.example)
a[end]!
assertEqual(self, a, array(array, self.typecode, self.example[begin:-1]))
a = array(array, self.typecode, self.example)
a[length(self.example) - 1]!
assertEqual(self, a, array(array, self.typecode, self.example[begin:-1]))
a = array(array, self.typecode, self.example)
a[-length(self.example)]!
assertEqual(self, a, array(array, self.typecode, self.example[2:end]))
assertRaises(self, TypeError, __delitem__(a))
assertRaises(self, TypeError, __delitem__(a), nothing)
assertRaises(self, IndexError, __delitem__(a), length(self.example))
assertRaises(self, IndexError, __delitem__(a), -length(self.example) - 1)
end

function test_getslice(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertEqual(self, a[begin:end], a)
assertEqual(self, a[2:end], array(array, self.typecode, self.example[2:end]))
assertEqual(self, a[begin:1], array(array, self.typecode, self.example[begin:1]))
assertEqual(self, a[begin:-1], array(array, self.typecode, self.example[begin:-1]))
assertEqual(self, a[end:end], array(array, self.typecode, self.example[end:end]))
assertEqual(self, a[end:end], array(array, self.typecode))
assertEqual(self, a[3:1], array(array, self.typecode))
assertEqual(self, a[1001:end], array(array, self.typecode))
assertEqual(self, a[end:end], a)
assertEqual(self, a[begin:1000], a)
assertEqual(self, a[begin:-1000], array(array, self.typecode))
assertEqual(self, a[end:end], a)
assertEqual(self, a[2001:1000], array(array, self.typecode))
end

function test_extended_getslice(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
indices = (0, nothing, 1, 3, 19, 100, maxsize(sys), -1, -2, -31, -100)
for start in indices
for stop in indices
for step in indices[2:end]
assertEqual(self, collect(a[(start + 1):stop]), collect(a)[(start + 1):stop])
end
end
end
end

function test_setslice(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
a[begin:1] = a
assertEqual(self, a, array(array, self.typecode, self.example + self.example[2:end]))
a = array(array, self.typecode, self.example)
a[begin:-1] = a
assertEqual(self, a, array(array, self.typecode, self.example + self.example[end:end]))
a = array(array, self.typecode, self.example)
a[end:end] = a
assertEqual(self, a, array(array, self.typecode, self.example[begin:-1] + self.example))
a = array(array, self.typecode, self.example)
a[2:end] = a
assertEqual(self, a, array(array, self.typecode, self.example[begin:1] + self.example))
a = array(array, self.typecode, self.example)
a[2:-1] = a
assertEqual(self, a, array(array, self.typecode, (self.example[begin:1] + self.example) + self.example[end:end]))
a = array(array, self.typecode, self.example)
a[1001:end] = a
assertEqual(self, a, array(array, self.typecode, 2*self.example))
a = array(array, self.typecode, self.example)
a[end:end] = a
assertEqual(self, a, array(array, self.typecode, self.example))
a = array(array, self.typecode, self.example)
a[begin:1000] = a
assertEqual(self, a, array(array, self.typecode, self.example))
a = array(array, self.typecode, self.example)
a[begin:-1000] = a
assertEqual(self, a, array(array, self.typecode, 2*self.example))
a = array(array, self.typecode, self.example)
a[2:0] = a
assertEqual(self, a, array(array, self.typecode, (self.example[begin:1] + self.example) + self.example[2:end]))
a = array(array, self.typecode, self.example)
a[2001:1000] = a
assertEqual(self, a, array(array, self.typecode, 2*self.example))
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, __setitem__(a), slice(0, 0), nothing)
assertRaises(self, TypeError, __setitem__(a), slice(0, 1), nothing)
b = array(array, badtypecode(self))
assertRaises(self, TypeError, __setitem__(a), slice(0, 0), b)
assertRaises(self, TypeError, __setitem__(a), slice(0, 1), b)
end

function test_extended_set_del_slice(self::AbstractBaseTest)
indices = (0, nothing, 1, 3, 19, 100, maxsize(sys), -1, -2, -31, -100)
for start in indices
for stop in indices
for step in indices[2:end]
a = array(array, self.typecode, self.example)
L = collect(a)
data = L[(start + 1):stop]
reverse(data)
L[(start + 1):stop] = data
a[(start + 1):stop] = array(array, self.typecode, data)
assertEqual(self, a, array(array, self.typecode, L))
L[(start + 1):stop]!
a[(start + 1):stop]!
assertEqual(self, a, array(array, self.typecode, L))
end
end
end
end

function test_index(self::AbstractBaseTest)
example = 2*self.example
a = array(array, self.typecode, example)
assertRaises(self, TypeError, index(a))
for x in example
assertEqual(self, index(a, x), index(example, x))
end
assertRaises(self, ValueError, index(a), nothing)
assertRaises(self, ValueError, index(a), self.outside)
a = array(array, "i", [-2, -1, 0, 0, 1, 2])
assertEqual(self, index(a, 0), 2)
assertEqual(self, index(a, 0, 2), 2)
assertEqual(self, index(a, 0, -4), 2)
assertEqual(self, index(a, -2, -10), 0)
assertEqual(self, index(a, 0, 3), 3)
assertEqual(self, index(a, 0, -3), 3)
assertEqual(self, index(a, 0, 3, 4), 3)
assertEqual(self, index(a, 0, -3, -2), 3)
assertRaises(self, ValueError, index(a), 2, 0, -10)
end

function test_count(self::AbstractBaseTest)
example = 2*self.example
a = array(array, self.typecode, example)
assertRaises(self, TypeError, count(a))
for x in example
assertEqual(self, count(a, x), count(example, x))
end
assertEqual(self, count(a, self.outside), 0)
assertEqual(self, count(a, nothing), 0)
end

function test_remove(self::AbstractBaseTest)
for x in self.example
example = 2*self.example
a = array(array, self.typecode, example)
pos = index(example, x)
example2 = example[begin:pos] + example[(pos + 1 + 1):end]
remove(a, x)
assertEqual(self, a, array(array, self.typecode, example2))
end
a = array(array, self.typecode, self.example)
assertRaises(self, ValueError, remove(a), self.outside)
assertRaises(self, ValueError, remove(a), nothing)
end

function test_pop(self::AbstractBaseTest)
a = array(array, self.typecode)
assertRaises(self, IndexError, pop(a))
a = array(array, self.typecode, 2*self.example)
assertRaises(self, TypeError, pop(a), 42, 42)
assertRaises(self, TypeError, pop(a), nothing)
assertRaises(self, IndexError, pop(a), length(a))
assertRaises(self, IndexError, pop(a), -length(a) - 1)
assertEntryEqual(self, pop(a, 0), self.example[1])
assertEqual(self, a, array(array, self.typecode, self.example[2:end] + self.example))
assertEntryEqual(self, pop(a, 1), self.example[3])
assertEqual(self, a, array(array, self.typecode, (self.example[2:2] + self.example[4:end]) + self.example))
assertEntryEqual(self, pop(a, 0), self.example[2])
assertEntryEqual(self, pop(a), self.example[end])
assertEqual(self, a, array(array, self.typecode, self.example[4:end] + self.example[begin:-1]))
end

function test_reverse(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, reverse(a), 42)
reverse(a)
assertEqual(self, a, array(array, self.typecode, self.example[begin:end]))
end

function test_extend(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, extend(a))
extend(a, array(array, self.typecode, self.example[begin:end]))
assertEqual(self, a, array(array, self.typecode, self.example + self.example[begin:end]))
a = array(array, self.typecode, self.example)
extend(a, a)
assertEqual(self, a, array(array, self.typecode, self.example + self.example))
b = array(array, badtypecode(self))
assertRaises(self, TypeError, extend(a), b)
a = array(array, self.typecode, self.example)
extend(a, self.example[begin:end])
assertEqual(self, a, array(array, self.typecode, self.example + self.example[begin:end]))
end

@resumable function test_constructor_with_iterable_argument(self::AbstractBaseTest)
a = array(array, self.typecode, iter(self.example))
b = array(array, self.typecode, self.example)
assertEqual(self, a, b)
assertRaises(self, TypeError, array(array), self.typecode, 10)
mutable struct A <: AbstractA

end
function __iter__(self)
throw(UnicodeError)
end

assertRaises(self, UnicodeError, array(array), self.typecode, A())
@resumable function B()
throw(UnicodeError)
@yield nothing
end

assertRaises(self, UnicodeError, array(array), self.typecode, B())
end

function test_coveritertraverse(self::AbstractBaseTest)
try
import gc
catch exn
if exn isa ImportError
skipTest(self, "gc module not available")
end
end
a = array(array, self.typecode)
l = [iter(a)]
push!(l, l)
collect(gc)
end

function test_buffer(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
m = memoryview(a)
expected = tobytes(m)
assertEqual(self, tobytes(a), expected)
assertEqual(self, tobytes(a)[1], expected[1])
assertRaises(self, BufferError, append(a), a[1])
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, extend(a), a[1:1])
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, remove(a), a[1])
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, pop(a), 0)
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, fromlist(a), tolist(a))
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, frombytes(a), tobytes(a))
assertEqual(self, tobytes(m), expected)
if self.typecode == "u"
assertRaises(self, BufferError, fromunicode(a), tounicode(a))
assertEqual(self, tobytes(m), expected)
end
assertRaises(self, BufferError, imul(operator), a, 2)
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, imul(operator), a, 0)
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, setitem(operator), a, slice(0, 0), a)
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, delitem(operator), a, 0)
assertEqual(self, tobytes(m), expected)
assertRaises(self, BufferError, delitem(operator), a, slice(0, 1))
assertEqual(self, tobytes(m), expected)
end

function test_weakref(self::AbstractBaseTest)
s = array(array, self.typecode, self.example)
p = proxy(weakref, s)
assertEqual(self, tobytes(p), tobytes(s))
s = nothing
gc_collect(support)
assertRaises(self, ReferenceError, len, p)
end

function test_bug_782369(self::AbstractBaseTest)
for i in (0:9)
b = array(array, "B", (0:63))
end
rc = getrefcount(sys, 10)
for i in (0:9)
b = array(array, "B", (0:63))
end
assertEqual(self, rc, getrefcount(sys, 10))
end

function test_subclass_with_kwargs(self::AbstractBaseTest)
ArraySubclassWithKwargs("b", 1)
end

function test_create_from_bytes(self::AbstractBaseTest)
a = array(array, "H", b"1234")
assertEqual(self, length(a)*itemsize(a), 4)
end

function test_sizeof_with_buffer(self::AbstractBaseTest)
a = array(array, self.typecode, self.example)
basesize = calcvobjsize(support, "Pn2Pi")
buffer_size = buffer_info(a)[2]*itemsize(a)
check_sizeof(support, self, a, basesize + buffer_size)
end

function test_sizeof_without_buffer(self::AbstractBaseTest)
a = array(array, self.typecode)
basesize = calcvobjsize(support, "Pn2Pi")
check_sizeof(support, self, a, basesize)
end

function test_initialize_with_unicode(self::AbstractBaseTest)
if self.typecode != "u"
assertRaises(self, TypeError) do cm 
a = array(array, self.typecode, "foo")
end
assertIn(self, "cannot use a str", string(exception(cm)))
assertRaises(self, TypeError) do cm 
a = array(array, self.typecode, array(array, "u", "foo"))
end
assertIn(self, "cannot use a unicode array", string(exception(cm)))
else
a = array(array, self.typecode, "foo")
a = array(array, self.typecode, array(array, "u", "foo"))
end
end

function test_obsolete_write_lock(self::AbstractBaseTest)
using _testcapi: getbuffer_with_null_view
a = array(array, "B", b"")
assertRaises(self, BufferError, getbuffer_with_null_view, a)
end

function test_free_after_iterating(self::AbstractBaseTest)
check_free_after_iterating(support, self, iter, array(array), (self.typecode))
check_free_after_iterating(support, self, reversed, array(array), (self.typecode))
end

mutable struct StringTest <: AbstractStringTest

end
function test_setitem(self::AbstractStringTest)
test_setitem(super())
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, __setitem__(a), 0, self.example[begin:2])
end

mutable struct UnicodeTest <: AbstractUnicodeTest
typecode::String
smallerexample::String
outside::String
minitemsize::Int64
example::String
biggerexample::String

                    UnicodeTest(typecode::String = "u", smallerexample::String = "☺ ﻾", outside::String = string("3"), minitemsize::Int64 = 2, example::String = "☺ ﻿", biggerexample::String = "☺﻿") =
                        new(typecode, smallerexample, outside, minitemsize, example, biggerexample)
end
function test_unicode(self::AbstractUnicodeTest)
@test_throws TypeError array(array)("b", "foo")
a = array(array, "u", " Âሴ")
fromunicode(a, " ")
fromunicode(a, "")
fromunicode(a, "")
fromunicode(a, "abcÿሴ")
s = tounicode(a)
@test (s == " Âሴ abcÿሴ")
@test (itemsize(a) == sizeof_wchar)
s = " =\"'a\bÿ ሴ"
a = array(array, "u", s)
@test (repr(a) == "array('u', '\x00=\"\'a\\b\x80ÿ\x00\x01ሴ')")
@test_throws TypeError fromunicode(a)()
end

function test_issue17223(self::AbstractUnicodeTest)
if sizeof_wchar == 4
invalid_str = b"\xff\xff\xff\xff"
else
skipTest(self, "specific to 32-bit wchar_t")
end
a = array(array, "u", invalid_str)
@test_throws ValueError tounicode(a)()
@test_throws ValueError str(a)
end

mutable struct NumberTest <: AbstractNumberTest
offset::Any
__slots__::Vector{String}

                    NumberTest(offset::Any, __slots__::Vector{String} = ["offset"]) =
                        new(offset, __slots__)
end
function test_extslice(self::AbstractNumberTest)
a = array(array, self.typecode, (0:4))
assertEqual(self, a[begin:end], a)
assertEqual(self, a[begin:end], array(array, self.typecode, [0, 2, 4]))
assertEqual(self, a[2:end], array(array, self.typecode, [1, 3]))
assertEqual(self, a[begin:end], array(array, self.typecode, [4, 3, 2, 1, 0]))
assertEqual(self, a[begin:end], array(array, self.typecode, [4, 2, 0]))
assertEqual(self, a[4:end], array(array, self.typecode, [3, 1]))
assertEqual(self, a[end:end], a)
assertEqual(self, a[101:-100], a[begin:end])
assertEqual(self, a[end:end], array(array, self.typecode, [0, 2, 4]))
assertEqual(self, a[1001:2000], array(array, self.typecode, []))
assertEqual(self, a[end:end], array(array, self.typecode, []))
end

function test_delslice(self::AbstractNumberTest)
a = array(array, self.typecode, (0:4))
a[begin:end]!
assertEqual(self, a, array(array, self.typecode, [1, 3]))
a = array(array, self.typecode, (0:4))
a[2:end]!
assertEqual(self, a, array(array, self.typecode, [0, 2, 4]))
a = array(array, self.typecode, (0:4))
a[2:end]!
assertEqual(self, a, array(array, self.typecode, [0, 2, 3, 4]))
a = array(array, self.typecode, (0:9))
a[begin:end]!
assertEqual(self, a, array(array, self.typecode, [1, 2, 3, 4, 5, 6, 7, 8, 9]))
a = array(array, self.typecode, (0:9))
a[10:end]!
end

function test_assignment(self::AbstractNumberTest)
a = array(array, self.typecode, (0:9))
a[begin:end] = array(array, self.typecode, repeat([42],5))
assertEqual(self, a, array(array, self.typecode, [42, 1, 42, 3, 42, 5, 42, 7, 42, 9]))
a = array(array, self.typecode, (0:9))
a[begin:end] = array(array, self.typecode, repeat([10],3))
assertEqual(self, a, array(array, self.typecode, [0, 10, 2, 3, 4, 10, 6, 7, 8, 10]))
a = array(array, self.typecode, (0:3))
a[begin:end] = a
assertEqual(self, a, array(array, self.typecode, [3, 2, 1, 0]))
a = array(array, self.typecode, (0:9))
b = a[begin:end]
c = a[begin:end]
ins = array(array, self.typecode, (0:1))
a[3:3] = ins
b[slice(2, 3)] = ins
c[3:3] = ins
end

function test_iterationcontains(self::AbstractNumberTest)
a = array(array, self.typecode, (0:9))
assertEqual(self, collect(a), collect((0:9)))
b = array(array, self.typecode, [20])
assertEqual(self, a[end] in a, true)
assertEqual(self, b[1] not in a, true)
end

function check_overflow(self::AbstractNumberTest, lower, upper)
a = array(array, self.typecode, [lower])
a[1] = lower
assertRaises(self, OverflowError, array(array), self.typecode, [lower - 1])
assertRaises(self, OverflowError, __setitem__(a), 0, lower - 1)
a = array(array, self.typecode, [upper])
a[1] = upper
assertRaises(self, OverflowError, array(array), self.typecode, [upper + 1])
assertRaises(self, OverflowError, __setitem__(a), 0, upper + 1)
end

function test_subclassing(self::AbstractNumberTest)
typecode = self.typecode
mutable struct ExaggeratingArray <: AbstractExaggeratingArray
offset::Any
__slots__::Vector{String}

                    ExaggeratingArray(offset::Any, __slots__::Vector{String} = ["offset"]) =
                        new(offset, __slots__)
end
function __new__(cls, typecode, data, offset)
return __new__(array.array, cls, typecode, data)
end

function __init__(self, typecode, data, offset)
self.offset = offset
end

function __getitem__(self, i)
return __getitem__(array.array, self) + self.offset
end

a = ExaggeratingArray(self.typecode, [3, 6, 7, 11], 4)
assertEntryEqual(self, a[1], 7)
assertRaises(self, AttributeError, setattr, a, "color", "blue")
end

function test_frombytearray(self::AbstractNumberTest)
a = array(array, "b", (0:9))
b = array(array, self.typecode, a)
assertEqual(self, a, b)
end

mutable struct IntegerNumberTest <: AbstractIntegerNumberTest

end
function test_type_error(self::AbstractIntegerNumberTest)
a = array(array, self.typecode)
append(a, 42)
assertRaises(self, TypeError) do 
append(a, 42.0)
end
assertRaises(self, TypeError) do 
a[1] = 42.0
end
end

mutable struct Intable <: AbstractIntable
_num::Any

                    Intable(_num::Any = num) =
                        new(_num)
end
function __index__(self::AbstractIntable)
return self._num
end

function __int__(self::AbstractIntable)
return self._num
end

function __sub__(self::AbstractIntable, other)::Intable
return Intable(Int(self) - Int(other))
end

function __add__(self::AbstractIntable, other)::Intable
return Intable(Int(self) + Int(other))
end

mutable struct SignedNumberTest <: AbstractSignedNumberTest
smallerexample::Vector{Int64}
outside::Int64
example::Vector{Int64}
biggerexample::Vector{Int64}

                    SignedNumberTest(smallerexample::Vector{Int64} = [-1, 0, 1, 42, 126], outside::Int64 = 23, example::Vector{Int64} = [-1, 0, 1, 42, 127], biggerexample::Vector{Int64} = [-1, 0, 1, 43, 127]) =
                        new(smallerexample, outside, example, biggerexample)
end
function test_overflow(self::AbstractSignedNumberTest)
a = array(array, self.typecode)
lower = -1*Int(pow(2, itemsize(a)*8 - 1))
upper = Int(pow(2, itemsize(a)*8 - 1)) - 1
check_overflow(self, lower, upper)
check_overflow(self, Intable(lower), Intable(upper))
end

mutable struct UnsignedNumberTest <: AbstractUnsignedNumberTest
smallerexample::Vector{Int64}
outside::Int64
example::Vector{Int64}
biggerexample::Vector{Int64}

                    UnsignedNumberTest(smallerexample::Vector{Int64} = [0, 1, 17, 23, 42, 254], outside::Int64 = 170, example::Vector{Int64} = [0, 1, 17, 23, 42, 255], biggerexample::Vector{Int64} = [0, 1, 17, 23, 43, 255]) =
                        new(smallerexample, outside, example, biggerexample)
end
function test_overflow(self::AbstractUnsignedNumberTest)
a = array(array, self.typecode)
lower = 0
upper = Int(pow(2, itemsize(a)*8)) - 1
check_overflow(self, lower, upper)
check_overflow(self, Intable(lower), Intable(upper))
end

function test_bytes_extend(self::AbstractUnsignedNumberTest)
s = bytes(self.example)
a = array(array, self.typecode, self.example)
extend(a, s)
assertEqual(self, a, array(array, self.typecode, self.example + self.example))
a = array(array, self.typecode, self.example)
extend(a, Vector{UInt8}(join(reversed(s), "")))
assertEqual(self, a, array(array, self.typecode, self.example + self.example[begin:end]))
end

mutable struct ByteTest <: AbstractByteTest
typecode::String
minitemsize::Int64

                    ByteTest(typecode::String = "b", minitemsize::Int64 = 1) =
                        new(typecode, minitemsize)
end

mutable struct UnsignedByteTest <: AbstractUnsignedByteTest
typecode::String
minitemsize::Int64

                    UnsignedByteTest(typecode::String = "B", minitemsize::Int64 = 1) =
                        new(typecode, minitemsize)
end

mutable struct ShortTest <: AbstractShortTest
typecode::String
minitemsize::Int64

                    ShortTest(typecode::String = "h", minitemsize::Int64 = 2) =
                        new(typecode, minitemsize)
end

mutable struct UnsignedShortTest <: AbstractUnsignedShortTest
typecode::String
minitemsize::Int64

                    UnsignedShortTest(typecode::String = "H", minitemsize::Int64 = 2) =
                        new(typecode, minitemsize)
end

mutable struct IntTest <: AbstractIntTest
typecode::String
minitemsize::Int64

                    IntTest(typecode::String = "i", minitemsize::Int64 = 2) =
                        new(typecode, minitemsize)
end

mutable struct UnsignedIntTest <: AbstractUnsignedIntTest
typecode::String
minitemsize::Int64

                    UnsignedIntTest(typecode::String = "I", minitemsize::Int64 = 2) =
                        new(typecode, minitemsize)
end

mutable struct LongTest <: AbstractLongTest
typecode::String
minitemsize::Int64

                    LongTest(typecode::String = "l", minitemsize::Int64 = 4) =
                        new(typecode, minitemsize)
end

mutable struct UnsignedLongTest <: AbstractUnsignedLongTest
typecode::String
minitemsize::Int64

                    UnsignedLongTest(typecode::String = "L", minitemsize::Int64 = 4) =
                        new(typecode, minitemsize)
end

mutable struct LongLongTest <: AbstractLongLongTest
typecode::String
minitemsize::Int64

                    LongLongTest(typecode::String = "q", minitemsize::Int64 = 8) =
                        new(typecode, minitemsize)
end

mutable struct UnsignedLongLongTest <: AbstractUnsignedLongLongTest
typecode::String
minitemsize::Int64

                    UnsignedLongLongTest(typecode::String = "Q", minitemsize::Int64 = 8) =
                        new(typecode, minitemsize)
end

mutable struct FPTest <: AbstractFPTest
smallerexample::Vector{Union{Float64, Int64}}
outside::Int64
example::Vector{Union{Float64, Int64}}
biggerexample::Vector{Union{Float64, Int64}}

                    FPTest(smallerexample::Vector{Union{Float64, Int64}} = [-42.0, 0, 42, 100000.0, -20000000000.0], outside::Int64 = 23, example::Vector{Union{Float64, Int64}} = [-42.0, 0, 42, 100000.0, -10000000000.0], biggerexample::Vector{Union{Float64, Int64}} = [-42.0, 0, 42, 100000.0, 10000000000.0]) =
                        new(smallerexample, outside, example, biggerexample)
end
function assertEntryEqual(self::AbstractFPTest, entry1, entry2)
assertAlmostEqual(self, entry1, entry2)
end

function test_nan(self::AbstractFPTest)
a = array(array, self.typecode, [float("nan")])
b = array(array, self.typecode, [float("nan")])
assertIs(self, a != b, true)
assertIs(self, a == b, false)
assertIs(self, a > b, false)
assertIs(self, a >= b, false)
assertIs(self, a < b, false)
assertIs(self, a <= b, false)
end

function test_byteswap(self::AbstractFPTest)
a = array(array, self.typecode, self.example)
assertRaises(self, TypeError, byteswap(a), 42)
if itemsize(a) in (1, 2, 4, 8)
b = array(array, self.typecode, self.example)
byteswap(b)
if itemsize(a) == 1
assertEqual(self, a, b)
else
assertNotEqual(self, tobytes(a), tobytes(b))
end
byteswap(b)
assertEqual(self, a, b)
end
end

mutable struct FloatTest <: AbstractFloatTest
typecode::String
minitemsize::Int64

                    FloatTest(typecode::String = "f", minitemsize::Int64 = 4) =
                        new(typecode, minitemsize)
end

mutable struct DoubleTest <: AbstractDoubleTest
typecode::String
minitemsize::Int64

                    DoubleTest(typecode::String = "d", minitemsize::Int64 = 8) =
                        new(typecode, minitemsize)
end
function test_alloc_overflow(self::AbstractDoubleTest)

a = array(array, "d", repeat([-1],65536))
try
a *= (maxsize / 65536) + 1
catch exn
if exn isa MemoryError
#= pass =#
end
end
b = array(array, "d", [2.71828183, 3.14159265, -1])
try
b*((maxsize / 3) + 1)
catch exn
if exn isa MemoryError
#= pass =#
end
end
end

mutable struct LargeArrayTest <: AbstractLargeArrayTest
typecode::String

                    LargeArrayTest(typecode::String = "b") =
                        new(typecode)
end
function example(self::AbstractLargeArrayTest, size)::Int64
base = array(array, self.typecode, [0, 1, 2, 3, 4, 5, 6, 7])*(size / 8)
base += array(array, self.typecode, repeat([99],(size % 8)) + [8, 9, 10, 11])
return base
end

function test_example_data(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (length(example) == size + 4)
end

function test_access(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (example[1] == 0)
@test (example[-(size + 4)] == 0)
@test (example[size] == 8)
@test (example[-3] == 8)
@test (example[size + 3] == 11)
@test (example[end] == 11)
end

function test_slice(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (collect(example[begin:4]) == [0, 1, 2, 3])
@test (collect(example[end:end]) == [8, 9, 10, 11])
part = example[2:-1]
@test (length(part) == size + 2)
@test (part[1] == 1)
@test (part[end] == 10)
part!
part = example[begin:end]
@test (length(part) == (size + 5) / 2)
@test (collect(part[begin:4]) == [0, 2, 4, 6])
if size % 2
@test (collect(part[end:end]) == [9, 11])
else
@test (collect(part[end:end]) == [8, 10])
end
end

function test_count(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (count(example, 0) == size / 8)
@test (count(example, 11) == 1)
end

function test_append(self::AbstractLargeArrayTest, size)
example = example(self, size)
append(example, 12)
@test (example[end] == 12)
end

function test_extend(self::AbstractLargeArrayTest, size)
example = example(self, size)
extend(example, iter([12, 13, 14, 15]))
@test (length(example) == size + 8)
@test (collect(example[end:end]) == [8, 9, 10, 11, 12, 13, 14, 15])
end

function test_frombytes(self::AbstractLargeArrayTest, size)
example = example(self, size)
frombytes(example, b"abcd")
@test (length(example) == size + 8)
@test (collect(example[end:end]) == [8, 9, 10, 11] + collect(b"abcd"))
end

function test_fromlist(self::AbstractLargeArrayTest, size)
example = example(self, size)
fromlist(example, [12, 13, 14, 15])
@test (length(example) == size + 8)
@test (collect(example[end:end]) == [8, 9, 10, 11, 12, 13, 14, 15])
end

function test_index(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (index(example, 0) == 0)
@test (index(example, 1) == 1)
@test (index(example, 7) == 7)
@test (index(example, 11) == size + 3)
end

function test_insert(self::AbstractLargeArrayTest, size)
example = example(self, size)
insert(example, 0, 12)
insert(example, 10, 13)
insert(example, size + 1, 14)
@test (length(example) == size + 7)
@test (example[1] == 12)
@test (example[11] == 13)
@test (example[size + 1] == 14)
end

function test_pop(self::AbstractLargeArrayTest, size)
example = example(self, size)
@test (pop(example, 0) == 0)
@test (example[1] == 1)
@test (pop(example, size + 1) == 10)
@test (example[size + 1] == 11)
@test (pop(example, 1) == 2)
@test (example[2] == 3)
@test (length(example) == size + 1)
@test (pop(example) == 11)
@test (length(example) == size)
end

function test_remove(self::AbstractLargeArrayTest, size)
example = example(self, size)
remove(example, 0)
@test (length(example) == size + 3)
@test (example[1] == 1)
remove(example, 10)
@test (length(example) == size + 2)
@test (example[size] == 9)
@test (example[size + 1] == 11)
end

function test_reverse(self::AbstractLargeArrayTest, size)
example = example(self, size)
reverse(example)
@test (length(example) == size + 4)
@test (example[1] == 11)
@test (example[4] == 8)
@test (example[end] == 0)
reverse(example)
@test (length(example) == size + 4)
@test (collect(example[begin:4]) == [0, 1, 2, 3])
@test (collect(example[end:end]) == [8, 9, 10, 11])
end

function test_tolist(self::AbstractLargeArrayTest, size)
example = example(self, size)
ls = tolist(example)
@test (length(ls) == length(example))
@test (ls[begin:8] == collect(example[begin:8]))
@test (ls[end:end] == collect(example[end:end]))
end

function main()
main()
end

main()
