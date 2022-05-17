#= Unit tests for the bytes and bytearray types.

XXX This is a mess.  Common tests should be unified with string_tests.py (and
the latter should be modernized).
 =#
using Test


using _testcapi: getbuffer_with_null_view




import copy
import functools

import tempfile
import textwrap







using test.support.script_helper: assert_python_failure
abstract type AbstractIndexable end
abstract type AbstractBaseBytesTest end
abstract type AbstractS end
abstract type AbstractX end
abstract type AbstractY end
abstract type AbstractB <: Abstractbytes end
abstract type AbstractC end
abstract type AbstractBadInt end
abstract type AbstractBadIterable end
abstract type AbstractBytesTest <: AbstractBaseBytesTest end
abstract type AbstractA end
abstract type AbstractIterationBlocked <: Abstractlist end
abstract type AbstractIntBlocked <: Abstractint end
abstract type AbstractBytesSubclassBlocked <: Abstractbytes end
abstract type AbstractBufferBlocked <: Abstractbytearray end
abstract type AbstractSubBytes <: Abstractbytes end
abstract type AbstractByteArrayTest <: AbstractBaseBytesTest end
abstract type AbstractAssortedBytesTest end
abstract type AbstractBytearrayPEP3137Test end
abstract type AbstractFixedStringTest end
abstract type AbstractByteArrayAsStringTest <: AbstractFixedStringTest end
abstract type AbstractBytesAsStringTest <: AbstractFixedStringTest end
abstract type AbstractSubclassTest end
abstract type AbstractB1 <: Abstractself.basetype end
abstract type AbstractB2 <: Abstractself.basetype end
abstract type AbstractByteArraySubclass <: Abstractbytearray end
abstract type AbstractBytesSubclass <: Abstractbytes end
abstract type AbstractOtherBytesSubclass <: Abstractbytes end
abstract type AbstractByteArraySubclassTest <: AbstractSubclassTest end
abstract type Abstractsubclass <: Abstractbytearray end
abstract type AbstractBytesSubclassTest <: AbstractSubclassTest end
if sys.flags.bytes_warning
function check_bytes_warnings(func)
function wrapper()
check_warnings(warnings_helper, ("", BytesWarning)) do 
return func(args..., kw)
end
end

return wrapper
end

else
function check_bytes_warnings(func)
return func
end

end
mutable struct Indexable <: AbstractIndexable
value
end
function __index__(self::Indexable)
return self.value
end

mutable struct BaseBytesTest <: AbstractBaseBytesTest
type2test
end
function test_basics(self::BaseBytesTest)
b = type2test(self)
assertEqual(self, type_(b), self.type2test)
assertEqual(self, b.__class__, self.type2test)
end

function test_copy(self::BaseBytesTest)
a = type2test(self, b"abcd")
for copy_method in (copy.copy, copy.deepcopy)
b = copy_method(a)
assertEqual(self, a, b)
assertEqual(self, type_(a), type_(b))
end
end

function test_empty_sequence(self::BaseBytesTest)
b = type2test(self)
assertEqual(self, length(b), 0)
assertRaises(self, IndexError, () -> b[1])
assertRaises(self, IndexError, () -> b[2])
assertRaises(self, IndexError, () -> b[sys.maxsize + 1])
assertRaises(self, IndexError, () -> b[sys.maxsize + 2])
assertRaises(self, IndexError, () -> b[10^100])
assertRaises(self, IndexError, () -> b[end])
assertRaises(self, IndexError, () -> b[end])
assertRaises(self, IndexError, () -> b[-(sys.maxsize) + 1])
assertRaises(self, IndexError, () -> b[-(sys.maxsize)])
assertRaises(self, IndexError, () -> b[-(sys.maxsize) - -1])
assertRaises(self, IndexError, () -> b[-(10^100) + 1])
end

function test_from_iterable(self::S)
b = type2test(self, 0:255)
assertEqual(self, length(b), 256)
assertEqual(self, collect(b), collect(0:255))
b = type2test(self, Set([42]))
assertEqual(self, b, b"*")
b = type2test(self, Set([43, 45]))
assertIn(self, tuple(b), Set([(43, 45), (45, 43)]))
b = type2test(self, (x for x in 0:255))
assertEqual(self, length(b), 256)
assertEqual(self, collect(b), collect(0:255))
b = type2test(self, (i for i in 0:255 if i % 2 ))
assertEqual(self, length(b), 128)
assertEqual(self, collect(b), collect(0:255)[end:2:2])
mutable struct S <: AbstractS

end
function __getitem__(self::S, i)
return (1, 2, 3)[i + 1]
end

b = type2test(self, S())
assertEqual(self, b, b"\x01\x02\x03")
end

function test_from_tuple(self::BaseBytesTest)
b = type2test(self, tuple(0:255))
assertEqual(self, length(b), 256)
assertEqual(self, collect(b), collect(0:255))
b = type2test(self, (1, 2, 3))
assertEqual(self, b, b"\x01\x02\x03")
end

function test_from_list(self::BaseBytesTest)
b = type2test(self, collect(0:255))
assertEqual(self, length(b), 256)
assertEqual(self, collect(b), collect(0:255))
b = type2test(self, [1, 2, 3])
assertEqual(self, b, b"\x01\x02\x03")
end

function test_from_mutating_list(self::Y)
mutable struct X <: AbstractX

end
function __index__(self::X)::Int64
clear(a)
return 42
end

a = [X(), X()]
assertEqual(self, bytes(a), b"*")
mutable struct Y <: AbstractY

end
function __index__(self::Y)::Int64
if length(a) < 1000
append(a, self)
end
return 42
end

a = [Y()]
assertEqual(self, bytes(a), repeat(b"*",1000))
end

function test_from_index(self::BaseBytesTest)
b = type2test(self, [Indexable(), Indexable(1), Indexable(254), Indexable(255)])
assertEqual(self, collect(b), [0, 1, 254, 255])
assertRaises(self, ValueError, self.type2test, [Indexable(-1)])
assertRaises(self, ValueError, self.type2test, [Indexable(256)])
end

function test_from_buffer(self::B)
a = type2test(self, array(array, "B", [1, 2, 3]))
assertEqual(self, a, b"\x01\x02\x03")
a = type2test(self, b"\x01\x02\x03")
assertEqual(self, a, b"\x01\x02\x03")
mutable struct B <: AbstractB

end
function __index__(self::B)
throw(TypeError)
end

assertEqual(self, type2test(self, B(b"foobar")), b"foobar")
end

function test_from_ssize(self::BaseBytesTest)
assertEqual(self, type2test(self, 0), b"")
assertEqual(self, type2test(self, 1), b"\x00")
assertEqual(self, type2test(self, 5), b"\x00\x00\x00\x00\x00")
assertRaises(self, ValueError, self.type2test, -1)
assertEqual(self, type2test(self, "0", "ascii"), b"0")
assertEqual(self, type2test(self, b"0"), b"0")
assertRaises(self, OverflowError, self.type2test, sys.maxsize + 1)
end

function test_constructor_type_errors(self::C)
assertRaises(self, TypeError, self.type2test, 0.0)
mutable struct C <: AbstractC

end

assertRaises(self, TypeError, self.type2test, ["0"])
assertRaises(self, TypeError, self.type2test, [0.0])
assertRaises(self, TypeError, self.type2test, [nothing])
assertRaises(self, TypeError, self.type2test, [C()])
assertRaises(self, TypeError, self.type2test, "ascii")
assertRaises(self, TypeError, self.type2test, "ignore")
assertRaises(self, TypeError, self.type2test, 0, "ascii")
assertRaises(self, TypeError, self.type2test, b"", "ascii")
assertRaises(self, TypeError, self.type2test, 0, "ignore")
assertRaises(self, TypeError, self.type2test, b"", "ignore")
assertRaises(self, TypeError, self.type2test, "")
assertRaises(self, TypeError, self.type2test, "", "ignore")
assertRaises(self, TypeError, self.type2test, "", b"ascii")
assertRaises(self, TypeError, self.type2test, "", "ascii", b"ignore")
end

function test_constructor_value_errors(self::BaseBytesTest)
assertRaises(self, ValueError, self.type2test, [-1])
assertRaises(self, ValueError, self.type2test, [-(sys.maxsize)])
assertRaises(self, ValueError, self.type2test, [-(sys.maxsize) - 1])
assertRaises(self, ValueError, self.type2test, [-(sys.maxsize) - 2])
assertRaises(self, ValueError, self.type2test, [-(10^100)])
assertRaises(self, ValueError, self.type2test, [256])
assertRaises(self, ValueError, self.type2test, [257])
assertRaises(self, ValueError, self.type2test, [sys.maxsize])
assertRaises(self, ValueError, self.type2test, [sys.maxsize + 1])
assertRaises(self, ValueError, self.type2test, [10^100])
end

function test_constructor_overflow(self::BaseBytesTest)
size = MAX_Py_ssize_t
assertRaises(self, (OverflowError, MemoryError), self.type2test, size)
try
Vector{UInt8}(size - 4)
catch exn
if exn isa (OverflowError, MemoryError)
#= pass =#
end
end
end

function test_constructor_exceptions(self::BadIterable)
mutable struct BadInt <: AbstractBadInt

end
function __index__(self::BadInt)
1 / 0
end

assertRaises(self, ZeroDivisionError, self.type2test, BadInt())
assertRaises(self, ZeroDivisionError, self.type2test, [BadInt()])
mutable struct BadIterable <: AbstractBadIterable

end
function __iter__(self::BadIterable)
1 / 0
end

assertRaises(self, ZeroDivisionError, self.type2test, BadIterable())
end

function test_compare(self::BaseBytesTest)
b1 = type2test(self, [1, 2, 3])
b2 = type2test(self, [1, 2, 3])
b3 = type2test(self, [1, 3])
assertEqual(self, b1, b2)
assertTrue(self, b2 != b3)
assertTrue(self, b1 <= b2)
assertTrue(self, b1 <= b3)
assertTrue(self, b1 < b3)
assertTrue(self, b1 >= b2)
assertTrue(self, b3 >= b2)
assertTrue(self, b3 > b2)
assertFalse(self, b1 != b2)
assertFalse(self, b2 == b3)
assertFalse(self, b1 > b2)
assertFalse(self, b1 > b3)
assertFalse(self, b1 >= b3)
assertFalse(self, b1 < b2)
assertFalse(self, b3 < b2)
assertFalse(self, b3 <= b2)
end

function test_compare_to_str(self::BaseBytesTest)
assertEqual(self, type2test(self, b"\x00a\x00b\x00c") == "abc", false)
assertEqual(self, type2test(self, b"\x00\x00\x00a\x00\x00\x00b\x00\x00\x00c") == "abc", false)
assertEqual(self, type2test(self, b"a\x00b\x00c\x00") == "abc", false)
assertEqual(self, type2test(self, b"a\x00\x00\x00b\x00\x00\x00c\x00\x00\x00") == "abc", false)
assertEqual(self, type2test(self) == string(), false)
assertEqual(self, type2test(self) != string(), true)
end

function test_reversed(self::BaseBytesTest)
input = collect(map(ord, "Hello"))
b = type2test(self, input)
output = collect(reversed(b))
reverse(input)
assertEqual(self, output, input)
end

function test_getslice(self::BaseBytesTest)
function by(s)
return type2test(self, map(ord, s))
end

b = by("Hello, world")
assertEqual(self, b[begin:5], by("Hello"))
assertEqual(self, b[2:5], by("ello"))
assertEqual(self, b[6:7], by(", "))
assertEqual(self, b[8:end], by("world"))
assertEqual(self, b[8:12], by("world"))
assertEqual(self, b[8:100], by("world"))
assertEqual(self, b[begin:-7], by("Hello"))
assertEqual(self, b[length(b) - -10:-7], by("ello"))
assertEqual(self, b[length(b) - -6:-5], by(", "))
assertEqual(self, b[length(b) - -4:end], by("world"))
assertEqual(self, b[length(b) - -4:12], by("world"))
assertEqual(self, b[length(b) - -4:100], by("world"))
assertEqual(self, b[length(b) - -99:5], by("Hello"))
end

function test_extended_getslice(self::BaseBytesTest)
L = collect(0:254)
b = type2test(self, L)
indices = (0, nothing, 1, 3, 19, 100, sys.maxsize, -1, -2, -31, -100)
for start in indices
for stop in indices
for step in indices[2:end]
assertEqual(self, b[stop:step:start + 1], type2test(self, L[stop:step:start + 1]))
end
end
end
end

function test_encoding(self::BaseBytesTest)
sample = "Hello world\nሴ噸骼"
for enc in ("utf-8", "utf-16")
b = type2test(self, sample, enc)
assertEqual(self, b, type2test(self, Vector{UInt8}(sample)))
end
assertRaises(self, UnicodeEncodeError, self.type2test, sample, "latin-1")
b = type2test(self, sample, "latin-1", "ignore")
assertEqual(self, b, type2test(self, sample[begin:-3], "utf-8"))
end

function test_decode(self::BaseBytesTest)
sample = "Hello world\nሴ噸骼"
for enc in ("utf-8", "utf-16")
b = type2test(self, sample, enc)
assertEqual(self, decode(b, enc), sample)
end
sample = "Hello world\nþÿ"
b = type2test(self, sample, "latin-1")
assertRaises(self, UnicodeDecodeError, b.decode, "utf-8")
assertEqual(self, decode(b, "utf-8", "ignore"), "Hello world\n")
assertEqual(self, decode(b, "ignore", "utf-8"), "Hello world\n")
assertEqual(self, decode(type2test(self, b"\xe2\x98\x83")), "☃")
end

function test_check_encoding_errors(self::BaseBytesTest)
invalid = "Boom, Shaka Laka, Boom!"
encodings = ("ascii", "utf8", "latin1")
code = dedent(textwrap, "\n            import sys\n            type2test = $(self.type2test.__name__)\n            encodings = $('encodings')\n\n            for data in (\'\', \'short string\'):\n                try:\n                    type2test(data, encoding=$('invalid'))\n                except LookupError:\n                    pass\n                else:\n                    sys.exit(21)\n\n                for encoding in encodings:\n                    try:\n                        type2test(data, encoding=encoding, errors=$('invalid'))\n                    except LookupError:\n                        pass\n                    else:\n                        sys.exit(22)\n\n            for data in (b\'\', b\'short string\'):\n                data = type2test(data)\n                print(repr(data))\n                try:\n                    data.decode(encoding=$('invalid'))\n                except LookupError:\n                    sys.exit(10)\n                else:\n                    sys.exit(23)\n\n                try:\n                    data.decode(errors=$('invalid'))\n                except LookupError:\n                    pass\n                else:\n                    sys.exit(24)\n\n                for encoding in encodings:\n                    try:\n                        data.decode(encoding=encoding, errors=$('invalid'))\n                    except LookupError:\n                        pass\n                    else:\n                        sys.exit(25)\n\n            sys.exit(10)\n        ")
proc = assert_python_failure("-X", "dev", "-c", code)
assertEqual(self, proc.rc, 10, proc)
end

function test_from_int(self::BaseBytesTest)
b = type2test(self, 0)
assertEqual(self, b, type2test(self))
b = type2test(self, 10)
assertEqual(self, b, type2test(self, repeat([0],10)))
b = type2test(self, 10000)
assertEqual(self, b, type2test(self, repeat([0],10000)))
end

function test_concat(self::BaseBytesTest)
b1 = type2test(self, b"abc")
b2 = type2test(self, b"def")
assertEqual(self, b1 + b2, b"abcdef")
assertEqual(self, b1 + bytes(b"def"), b"abcdef")
assertEqual(self, bytes(b"def") + b1, b"defabc")
assertRaises(self, TypeError, () -> b1 + "def")
assertRaises(self, TypeError, () -> "abc" + b2)
end

function test_repeat(self::BaseBytesTest)
for b in (b"abc", type2test(self, b"abc"))
assertEqual(self, b*3, b"abcabcabc")
assertEqual(self, b*0, b"")
assertEqual(self, b*-1, b"")
assertRaises(self, TypeError, () -> b*3.14)
assertRaises(self, TypeError, () -> 3.14*b)
assertRaises(self, (OverflowError, MemoryError)) do 
c = b*sys.maxsize
end
assertRaises(self, (OverflowError, MemoryError)) do 
b *= sys.maxsize
end
end
end

function test_repeat_1char(self::BaseBytesTest)
assertEqual(self, type2test(self, b"x")*100, type2test(self, repeat([ord("x")],100)))
end

function test_contains(self::BaseBytesTest)
b = type2test(self, b"abc")
assertIn(self, ord("a"), b)
assertIn(self, parse(Int, ord("a")), b)
assertNotIn(self, 200, b)
assertRaises(self, ValueError, () -> 300 ∈ b)
assertRaises(self, ValueError, () -> -1 ∈ b)
assertRaises(self, ValueError, () -> (sys.maxsize + 1) ∈ b)
assertRaises(self, TypeError, () -> nothing ∈ b)
assertRaises(self, TypeError, () -> float(ord("a")) ∈ b)
assertRaises(self, TypeError, () -> "a" ∈ b)
for f in (bytes, bytearray)
assertIn(self, f(b""), b)
assertIn(self, f(b"a"), b)
assertIn(self, f(b"b"), b)
assertIn(self, f(b"c"), b)
assertIn(self, f(b"ab"), b)
assertIn(self, f(b"bc"), b)
assertIn(self, f(b"abc"), b)
assertNotIn(self, f(b"ac"), b)
assertNotIn(self, f(b"d"), b)
assertNotIn(self, f(b"dab"), b)
assertNotIn(self, f(b"abd"), b)
end
end

function test_fromhex(self::BaseBytesTest)
assertRaises(self, TypeError, self.type2test.fromhex)
assertRaises(self, TypeError, self.type2test.fromhex, 1)
assertEqual(self, fromhex(self.type2test, ""), type2test(self))
b = Vector{UInt8}([26, 43, 48])
assertEqual(self, fromhex(self.type2test, "1a2B30"), b)
assertEqual(self, fromhex(self.type2test, "  1A 2B  30   "), b)
assertEqual(self, fromhex(self.type2test, " 1A\n2B\t30\v"), b)
for c in "\t\n\v\f\r "
assertEqual(self, fromhex(self.type2test, c), type2test(self))
end
for c in "    "
assertRaises(self, ValueError, self.type2test.fromhex, c)
end
assertEqual(self, fromhex(self.type2test, "0000"), b"\x00\x00")
assertRaises(self, TypeError, self.type2test.fromhex, b"1B")
assertRaises(self, ValueError, self.type2test.fromhex, "a")
assertRaises(self, ValueError, self.type2test.fromhex, "rt")
assertRaises(self, ValueError, self.type2test.fromhex, "1a b cd")
assertRaises(self, ValueError, self.type2test.fromhex, " ")
assertRaises(self, ValueError, self.type2test.fromhex, "12       34")
for (data, pos) in (("12 x4 56", 3), ("12 3x 56", 4), ("12 xy 56", 3), ("12 3ÿ 56", 4))
assertRaises(self, ValueError) do cm 
fromhex(self.type2test, data)
end
assertIn(self, "at position %s" % pos, string(cm.exception))
end
end

function test_hex(self::BaseBytesTest)
assertRaises(self, TypeError, self.type2test.hex)
assertRaises(self, TypeError, self.type2test.hex, 1)
assertEqual(self, hex(type2test(self, b"")), "")
assertEqual(self, hex(Vector{UInt8}([26, 43, 48])), "1a2b30")
assertEqual(self, hex(type2test(self, b"\x1a+0")), "1a2b30")
assertEqual(self, hex(memoryview(b"\x1a+0")), "1a2b30")
end

function test_hex_separator_basics(self::BaseBytesTest)
three_bytes = type2test(self, b"\xb9\x01\xef")
assertEqual(self, hex(three_bytes), "b901ef")
assertRaises(self, ValueError) do 
hex(three_bytes, "")
end
assertRaises(self, ValueError) do 
hex(three_bytes, "xx")
end
assertEqual(self, hex(three_bytes, ":", 0), "b901ef")
assertRaises(self, TypeError) do 
hex(three_bytes, nothing, 0)
end
assertRaises(self, ValueError) do 
hex(three_bytes, "ÿ")
end
assertRaises(self, ValueError) do 
hex(three_bytes, b"\xff")
end
assertRaises(self, ValueError) do 
hex(three_bytes, b"\x80")
end
assertRaises(self, ValueError) do 
hex(three_bytes, chr(256))
end
assertEqual(self, hex(three_bytes, ":", 0), "b901ef")
assertEqual(self, hex(three_bytes, b"\x00"), "b9 01 ef")
assertEqual(self, hex(three_bytes, " "), "b9 01 ef")
assertEqual(self, hex(three_bytes, b"\x7f"), "b901ef")
assertEqual(self, hex(three_bytes, ""), "b901ef")
assertEqual(self, hex(three_bytes, ":", 3), "b901ef")
assertEqual(self, hex(three_bytes, ":", 4), "b901ef")
assertEqual(self, hex(three_bytes, ":", -4), "b901ef")
assertEqual(self, hex(three_bytes, ":"), "b9:01:ef")
assertEqual(self, hex(three_bytes, b"$"), "b9\$01\$ef")
assertEqual(self, hex(three_bytes, ":", 1), "b9:01:ef")
assertEqual(self, hex(three_bytes, ":", -1), "b9:01:ef")
assertEqual(self, hex(three_bytes, ":", 2), "b9:01ef")
assertEqual(self, hex(three_bytes, ":", 1), "b9:01:ef")
assertEqual(self, hex(three_bytes, "*", -2), "b901*ef")
value = b"{s\x05\x00\x00\x00worldi\x02\x00\x00\x00s\x05\x00\x00\x00helloi\x01\x00\x00\x000"
assertEqual(self, hex(value, ".", 8), "7b7305000000776f.726c646902000000.730500000068656c.6c6f690100000030")
end

function test_hex_separator_five_bytes(self::BaseBytesTest)
five_bytes = type2test(self, 90:94)
assertEqual(self, hex(five_bytes), "5a5b5c5d5e")
end

function test_hex_separator_six_bytes(self::BaseBytesTest)
six_bytes = type2test(self, (x*3 for x in 1:6))
assertEqual(self, hex(six_bytes), "0306090c0f12")
assertEqual(self, hex(six_bytes, ".", 1), "03.06.09.0c.0f.12")
assertEqual(self, hex(six_bytes, " ", 2), "0306 090c 0f12")
assertEqual(self, hex(six_bytes, "-", 3), "030609-0c0f12")
assertEqual(self, hex(six_bytes, ":", 4), "0306:090c0f12")
assertEqual(self, hex(six_bytes, ":", 5), "03:06090c0f12")
assertEqual(self, hex(six_bytes, ":", 6), "0306090c0f12")
assertEqual(self, hex(six_bytes, ":", 95), "0306090c0f12")
assertEqual(self, hex(six_bytes, "_", -3), "030609_0c0f12")
assertEqual(self, hex(six_bytes, ":", -4), "0306090c:0f12")
assertEqual(self, hex(six_bytes, b"@", -5), "0306090c0f@12")
assertEqual(self, hex(six_bytes, ":", -6), "0306090c0f12")
assertEqual(self, hex(six_bytes, " ", -95), "0306090c0f12")
end

function test_join(self::BaseBytesTest)
assertEqual(self, join([], type2test(self, b"")), b"")
assertEqual(self, join([b""], type2test(self, b"")), b"")
for lst in [[b"abc"], [b"a", b"bc"], [b"ab", b"c"], [b"a", b"b", b"c"]]
lst = collect(map(self.type2test, lst))
assertEqual(self, join(lst, type2test(self, b"")), b"abc")
assertEqual(self, join(tuple(lst), type2test(self, b"")), b"abc")
assertEqual(self, join((x for x in lst), type2test(self, b"")), b"abc")
end
dot_join = x -> join(x, type2test(self, b".:"))
assertEqual(self, dot_join([b"ab", b"cd"]), b"ab.:cd")
assertEqual(self, dot_join([memoryview(b"ab"), b"cd"]), b"ab.:cd")
assertEqual(self, dot_join([b"ab", memoryview(b"cd")]), b"ab.:cd")
assertEqual(self, dot_join([Vector{UInt8}(b"ab"), b"cd"]), b"ab.:cd")
assertEqual(self, dot_join([b"ab", Vector{UInt8}(b"cd")]), b"ab.:cd")
seq = repeat([b"abc"],100000)
expected = append!(b"abc", repeat(b".:abc",99999))
assertEqual(self, dot_join(seq), expected)
seq = repeat([b"abc"],100000)
expected = repeat(b"abc",100000)
assertEqual(self, join(seq, type2test(self, b"")), expected)
assertRaises(self, TypeError, x -> join(x, type2test(self, b" ")), nothing)
assertRaises(self, TypeError) do 
dot_join([Vector{UInt8}(b"ab"), "cd", b"ef"])
end
assertRaises(self, TypeError) do 
dot_join([memoryview(b"ab"), "cd", b"ef"])
end
end

function test_count(self::BaseBytesTest)
b = type2test(self, b"mississippi")
i = 105
p = 112
w = 119
assertEqual(self, count(b, b"i"), 4)
assertEqual(self, count(b, b"ss"), 2)
assertEqual(self, count(b, b"w"), 0)
assertEqual(self, count(b, i), 4)
assertEqual(self, count(b, w), 0)
assertEqual(self, count(b, b"i", 6), 2)
assertEqual(self, count(b, b"p", 6), 2)
assertEqual(self, count(b, b"i", 1, 3), 1)
assertEqual(self, count(b, b"p", 7, 9), 1)
assertEqual(self, count(b, i, 6), 2)
assertEqual(self, count(b, p, 6), 2)
assertEqual(self, count(b, i, 1, 3), 1)
assertEqual(self, count(b, p, 7, 9), 1)
end

function test_startswith(self::BaseBytesTest)
b = type2test(self, b"hello")
assertFalse(self, startswith(type2test(self), b"anything"))
assertTrue(self, startswith(b, b"hello"))
assertTrue(self, startswith(b, b"hel"))
assertTrue(self, startswith(b, b"h"))
assertFalse(self, startswith(b, b"hellow"))
assertFalse(self, startswith(b, b"ha"))
assertRaises(self, TypeError) do cm 
startswith(b, [b"h"])
end
exc = string(cm.exception)
assertIn(self, "bytes", exc)
assertIn(self, "tuple", exc)
end

function test_endswith(self::BaseBytesTest)
b = type2test(self, b"hello")
assertFalse(self, endswith(Vector{UInt8}(), b"anything"))
assertTrue(self, endswith(b, b"hello"))
assertTrue(self, endswith(b, b"llo"))
assertTrue(self, endswith(b, b"o"))
assertFalse(self, endswith(b, b"whello"))
assertFalse(self, endswith(b, b"no"))
assertRaises(self, TypeError) do cm 
endswith(b, [b"o"])
end
exc = string(cm.exception)
assertIn(self, "bytes", exc)
assertIn(self, "tuple", exc)
end

function test_find(self::BaseBytesTest)
b = type2test(self, b"mississippi")
i = 105
w = 119
assertEqual(self, find(b, b"ss"), 2)
assertEqual(self, find(b, b"w"), -1)
assertEqual(self, find(b, b"mississippian"), -1)
assertEqual(self, find(b, i), 1)
assertEqual(self, find(b, w), -1)
assertEqual(self, find(b, b"ss", 3), 5)
assertEqual(self, find(b, b"ss", 1, 7), 2)
assertEqual(self, find(b, b"ss", 1, 3), -1)
assertEqual(self, find(b, i, 6), 7)
assertEqual(self, find(b, i, 1, 3), 1)
assertEqual(self, find(b, w, 1, 3), -1)
for index in (-1, 256, sys.maxsize + 1)
assertRaisesRegex(self, ValueError, "byte must be in range\\(0, 256\\)", b.find, index)
end
end

function test_rfind(self::BaseBytesTest)
b = type2test(self, b"mississippi")
i = 105
w = 119
assertEqual(self, rfind(b, b"ss"), 5)
assertEqual(self, rfind(b, b"w"), -1)
assertEqual(self, rfind(b, b"mississippian"), -1)
assertEqual(self, rfind(b, i), 10)
assertEqual(self, rfind(b, w), -1)
assertEqual(self, rfind(b, b"ss", 3), 5)
assertEqual(self, rfind(b, b"ss", 0, 6), 2)
assertEqual(self, rfind(b, i, 1, 3), 1)
assertEqual(self, rfind(b, i, 3, 9), 7)
assertEqual(self, rfind(b, w, 1, 3), -1)
end

function test_index(self::BaseBytesTest)
b = type2test(self, b"mississippi")
i = 105
w = 119
assertEqual(self, index(b, b"ss"), 2)
assertRaises(self, ValueError, b.index, b"w")
assertRaises(self, ValueError, b.index, b"mississippian")
assertEqual(self, index(b, i), 1)
assertRaises(self, ValueError, b.index, w)
assertEqual(self, index(b, b"ss", 3), 5)
assertEqual(self, index(b, b"ss", 1, 7), 2)
assertRaises(self, ValueError, b.index, b"ss", 1, 3)
assertEqual(self, index(b, i, 6), 7)
assertEqual(self, index(b, i, 1, 3), 1)
assertRaises(self, ValueError, b.index, w, 1, 3)
end

function test_rindex(self::BaseBytesTest)
b = type2test(self, b"mississippi")
i = 105
w = 119
assertEqual(self, rindex(b, b"ss"), 5)
assertRaises(self, ValueError, b.rindex, b"w")
assertRaises(self, ValueError, b.rindex, b"mississippian")
assertEqual(self, rindex(b, i), 10)
assertRaises(self, ValueError, b.rindex, w)
assertEqual(self, rindex(b, b"ss", 3), 5)
assertEqual(self, rindex(b, b"ss", 0, 6), 2)
assertEqual(self, rindex(b, i, 1, 3), 1)
assertEqual(self, rindex(b, i, 3, 9), 7)
assertRaises(self, ValueError, b.rindex, w, 1, 3)
end

function test_mod(self::BaseBytesTest)
b = type2test(self, b"hello, %b!")
orig = b
b = b % b"world"
assertEqual(self, b, b"hello, world!")
assertEqual(self, orig, b"hello, %b!")
assertFalse(self, b == orig)
b = type2test(self, b"%s / 100 = %d%%")
a = b % (b"seventy-nine", 79)
assertEqual(self, a, b"seventy-nine / 100 = 79%")
assertIs(self, type_(a), self.type2test)
b = type2test(self, b"hello,\x00%b!")
b = b % b"world"
assertEqual(self, b, b"hello,\x00world!")
assertIs(self, type_(b), self.type2test)
end

function test_imod(self::BaseBytesTest)
b = type2test(self, b"hello, %b!")
orig = b
b %= b"world"
assertEqual(self, b, b"hello, world!")
assertEqual(self, orig, b"hello, %b!")
assertFalse(self, b == orig)
b = type2test(self, b"%s / 100 = %d%%")
b %= (b"seventy-nine", 79)
assertEqual(self, b, b"seventy-nine / 100 = 79%")
assertIs(self, type_(b), self.type2test)
b = type2test(self, b"hello,\x00%b!")
b %= b"world"
assertEqual(self, b, b"hello,\x00world!")
assertIs(self, type_(b), self.type2test)
end

function test_rmod(self::BaseBytesTest)
assertRaises(self, TypeError) do 
object() % type2test(self, b"abc")
end
assertIs(self, __rmod__(type2test(self, b"abc"), "%r"), NotImplemented)
end

function test_replace(self::BaseBytesTest)
b = type2test(self, b"mississippi")
assertEqual(self, replace(b, b"i", b"a"), b"massassappa")
assertEqual(self, replace(b, b"ss", b"x"), b"mixixippi")
end

function test_replace_int_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"a b").replace, 32, b"")
end

function test_split_string_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"a b").split, " ")
assertRaises(self, TypeError, type2test(self, b"a b").rsplit, " ")
end

function test_split_int_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"a b").split, 32)
assertRaises(self, TypeError, type2test(self, b"a b").rsplit, 32)
end

function test_split_unicodewhitespace(self::BaseBytesTest)
for b in (b"a\x1cb", b"a\x1db", b"a\x1eb", b"a\x1fb")
b = type2test(self, b)
assertEqual(self, split(b), [b])
end
b = type2test(self, b"\t\n\x0b\x0c\r\x1c\x1d\x1e\x1f")
assertEqual(self, split(b), [b"\x1c\x1d\x1e\x1f"])
end

function test_rsplit_unicodewhitespace(self::BaseBytesTest)
b = type2test(self, b"\t\n\x0b\x0c\r\x1c\x1d\x1e\x1f")
assertEqual(self, rsplit(b), [b"\x1c\x1d\x1e\x1f"])
end

function test_partition(self::BaseBytesTest)
b = type2test(self, b"mississippi")
assertEqual(self, partition(b, b"ss"), (b"mi", b"ss", b"issippi"))
assertEqual(self, partition(b, b"w"), (b"mississippi", b"", b""))
end

function test_rpartition(self::BaseBytesTest)
b = type2test(self, b"mississippi")
assertEqual(self, rpartition(b, b"ss"), (b"missi", b"ss", b"ippi"))
assertEqual(self, rpartition(b, b"i"), (b"mississipp", b"i", b""))
assertEqual(self, rpartition(b, b"w"), (b"", b"", b"mississippi"))
end

function test_partition_string_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"a b").partition, " ")
assertRaises(self, TypeError, type2test(self, b"a b").rpartition, " ")
end

function test_partition_int_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"a b").partition, 32)
assertRaises(self, TypeError, type2test(self, b"a b").rpartition, 32)
end

function test_pickling(self::BaseBytesTest)
for proto in 0:pickle.HIGHEST_PROTOCOL
for b in (b"", b"a", b"abc", b"\xffab\x80", b"\x00\x00\xff\x00\x00")
b = type2test(self, b)
ps = dumps(pickle, b, proto)
q = loads(pickle, ps)
assertEqual(self, b, q)
end
end
end

function test_iterator_pickling(self::BaseBytesTest)
for proto in 0:pickle.HIGHEST_PROTOCOL
for b in (b"", b"a", b"abc", b"\xffab\x80", b"\x00\x00\xff\x00\x00")
it = (x for x in type2test(self, b))
itorg = (x for x in type2test(self, b))
data = collect(type2test(self, b))
d = dumps(pickle, it, proto)
it = loads(pickle, d)
assertEqual(self, type_(itorg), type_(it))
assertEqual(self, collect(it), data)
it = loads(pickle, d)
if !(b)
continue;
end
next(it)
d = dumps(pickle, it, proto)
it = loads(pickle, d)
assertEqual(self, collect(it), data[2:end])
end
end
end

function test_strip_bytearray(self::BaseBytesTest)
assertEqual(self, strip(type2test(self, b"abc"), memoryview(b"ac")), b"b")
assertEqual(self, lstrip(type2test(self, b"abc"), memoryview(b"ac")), b"bc")
assertEqual(self, rstrip(type2test(self, b"abc"), memoryview(b"ac")), b"ab")
end

function test_strip_string_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"abc").strip, "ac")
assertRaises(self, TypeError, type2test(self, b"abc").lstrip, "ac")
assertRaises(self, TypeError, type2test(self, b"abc").rstrip, "ac")
end

function test_strip_int_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b" abc ").strip, 32)
assertRaises(self, TypeError, type2test(self, b" abc ").lstrip, 32)
assertRaises(self, TypeError, type2test(self, b" abc ").rstrip, 32)
end

function test_center(self::BaseBytesTest)
b = type2test(self, b"abc")
for fill_type in (bytes, bytearray)
assertEqual(self, center(b, 7, fill_type(b"-")), type2test(self, b"--abc--"))
end
end

function test_ljust(self::BaseBytesTest)
b = type2test(self, b"abc")
for fill_type in (bytes, bytearray)
assertEqual(self, ljust(b, 7, fill_type(b"-")), type2test(self, b"abc----"))
end
end

function test_rjust(self::BaseBytesTest)
b = type2test(self, b"abc")
for fill_type in (bytes, bytearray)
assertEqual(self, rjust(b, 7, fill_type(b"-")), type2test(self, b"----abc"))
end
end

function test_xjust_int_error(self::BaseBytesTest)
assertRaises(self, TypeError, type2test(self, b"abc").center, 7, 32)
assertRaises(self, TypeError, type2test(self, b"abc").ljust, 7, 32)
assertRaises(self, TypeError, type2test(self, b"abc").rjust, 7, 32)
end

function test_ord(self::BaseBytesTest)
b = type2test(self, b"\x00A\x7f\x80\xff")
assertEqual(self, [ord(b[i + 1:i + 1]) for i in 0:length(b) - 1], [0, 65, 127, 128, 255])
end

function test_maketrans(self::BaseBytesTest)
transtable = b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x0b\x0c\r\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`xyzdefghijklmnopqrstuvwxyz{|}~\x7f\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7\xc8\xc9\xca\xcb\xcc\xcd\xce\xcf\xd0\xd1\xd2\xd3\xd4\xd5\xd6\xd7\xd8\xd9\xda\xdb\xdc\xdd\xde\xdf\xe0\xe1\xe2\xe3\xe4\xe5\xe6\xe7\xe8\xe9\xea\xeb\xec\xed\xee\xef\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9\xfa\xfb\xfc\xfd\xfe\xff"
assertEqual(self, maketrans(self.type2test, b"abc", b"xyz"), transtable)
transtable = b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x0b\x0c\r\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7f\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7\xc8\xc9\xca\xcb\xcc\xcd\xce\xcf\xd0\xd1\xd2\xd3\xd4\xd5\xd6\xd7\xd8\xd9\xda\xdb\xdc\xdd\xde\xdf\xe0\xe1\xe2\xe3\xe4\xe5\xe6\xe7\xe8\xe9\xea\xeb\xec\xed\xee\xef\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9\xfa\xfb\xfcxyz"
assertEqual(self, maketrans(self.type2test, b"\xfd\xfe\xff", b"xyz"), transtable)
assertRaises(self, ValueError, self.type2test.maketrans, b"abc", b"xyzq")
assertRaises(self, TypeError, self.type2test.maketrans, "abc", "def")
end

function test_none_arguments(self::BaseBytesTest)
b = type2test(self, b"hello")
l = type2test(self, b"l")
h = type2test(self, b"h")
x = type2test(self, b"x")
o = type2test(self, b"o")
assertEqual(self, 2, find(b, l, nothing))
assertEqual(self, 3, find(b, l, -2, nothing))
assertEqual(self, 2, find(b, l, nothing, -2))
assertEqual(self, 0, find(b, h, nothing, nothing))
assertEqual(self, 3, rfind(b, l, nothing))
assertEqual(self, 3, rfind(b, l, -2, nothing))
assertEqual(self, 2, rfind(b, l, nothing, -2))
assertEqual(self, 0, rfind(b, h, nothing, nothing))
assertEqual(self, 2, index(b, l, nothing))
assertEqual(self, 3, index(b, l, -2, nothing))
assertEqual(self, 2, index(b, l, nothing, -2))
assertEqual(self, 0, index(b, h, nothing, nothing))
assertEqual(self, 3, rindex(b, l, nothing))
assertEqual(self, 3, rindex(b, l, -2, nothing))
assertEqual(self, 2, rindex(b, l, nothing, -2))
assertEqual(self, 0, rindex(b, h, nothing, nothing))
assertEqual(self, 2, count(b, l, nothing))
assertEqual(self, 1, count(b, l, -2, nothing))
assertEqual(self, 1, count(b, l, nothing, -2))
assertEqual(self, 0, count(b, x, nothing, nothing))
assertEqual(self, true, endswith(b, o, nothing))
assertEqual(self, true, endswith(b, o, -2, nothing))
assertEqual(self, true, endswith(b, l, nothing, -2))
assertEqual(self, false, endswith(b, x, nothing, nothing))
assertEqual(self, true, startswith(b, h, nothing))
assertEqual(self, true, startswith(b, l, -2, nothing))
assertEqual(self, true, startswith(b, h, nothing, -2))
assertEqual(self, false, startswith(b, x, nothing, nothing))
end

function test_integer_arguments_out_of_byte_range(self::BaseBytesTest)
b = type2test(self, b"hello")
for method in (b.count, b.find, b.index, b.rfind, b.rindex)
assertRaises(self, ValueError, method, -1)
assertRaises(self, ValueError, method, 256)
assertRaises(self, ValueError, method, 9999)
end
end

function test_find_etc_raise_correct_error_messages(self::BaseBytesTest)
b = type2test(self, b"hello")
x = type2test(self, b"x")
assertRaisesRegex(self, TypeError, "\\bfind\\b", b.find, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\brfind\\b", b.rfind, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\bindex\\b", b.index, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\brindex\\b", b.rindex, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\bcount\\b", b.count, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\bstartswith\\b", b.startswith, x, nothing, nothing, nothing)
assertRaisesRegex(self, TypeError, "\\bendswith\\b", b.endswith, x, nothing, nothing, nothing)
end

function test_free_after_iterating(self::BaseBytesTest)
check_free_after_iterating(test.support, self, iter, self.type2test)
check_free_after_iterating(test.support, self, reversed, self.type2test)
end

function test_translate(self::BaseBytesTest)
b = type2test(self, b"hello")
rosetta = Vector{UInt8}(0:255)
rosetta[ord("o") + 1] = ord("e")
assertRaises(self, TypeError, b.translate)
assertRaises(self, TypeError, b.translate, nothing, nothing)
assertRaises(self, ValueError, b.translate, bytes(0:254))
c = replace!(rosetta, b"hello")
assertEqual(self, b, b"hello")
assertIsInstance(self, c, self.type2test)
c = translate(b, rosetta)
d = replace!(rosetta, b"")
assertEqual(self, c, d)
assertEqual(self, c, b"helle")
c = replace!(rosetta, b"l")
assertEqual(self, c, b"hee")
c = replace!(nothing, b"e")
assertEqual(self, c, b"hllo")
c = replace!(rosetta, b"")
assertEqual(self, c, b"helle")
c = replace!(rosetta, b"l")
assertEqual(self, c, b"hee")
c = replace!(nothing, b"e")
assertEqual(self, c, b"hllo")
end

function test_sq_item(self::BaseBytesTest)
_testcapi = import_module(import_helper, "_testcapi")
obj = type2test(self, (42,))
assertRaises(self, IndexError) do 
sequence_getitem(_testcapi, obj, -2)
end
assertRaises(self, IndexError) do 
sequence_getitem(_testcapi, obj, 1)
end
assertEqual(self, sequence_getitem(_testcapi, obj, 0), 42)
end

mutable struct BytesTest <: AbstractBytesTest
__bytes__
type2test

                    BytesTest(__bytes__ = nothing, type2test = bytes) =
                        new(__bytes__, type2test)
end
function test_getitem_error(self::BytesTest)
b = b"python"
msg = "byte indices must be integers or slices"
assertRaisesRegex(self, TypeError, msg) do 
b["a"]
end
end

function test_buffer_is_readonly(self::BytesTest)
fd = readline(os)
readline(fd) do f 
@test_throws TypeError f.readinto(b"")
end
end

function test_custom(self::A)
mutable struct A <: AbstractA

end
function __bytes__(self::A)::Array{UInt8}
return b"abc"
end

assertEqual(self, bytes(A()), b"abc")
mutable struct A <: AbstractA

end

assertRaises(self, TypeError, bytes, A())
mutable struct A <: AbstractA

end
function __bytes__(self::A)
return nothing
end

assertRaises(self, TypeError, bytes, A())
mutable struct A <: AbstractA

end
function __bytes__(self::A)::Array{UInt8}
return b"a"
end

function __index__(self::A)::Int64
return 42
end

assertEqual(self, bytes(A()), b"a")
mutable struct A <: AbstractA

end
function __bytes__(self::A)::Array{UInt8}
return b"abc"
end

assertEqual(self, bytes(A("€")), b"abc")
assertEqual(self, bytes(A("€"), "iso8859-15"), b"\xa4")
mutable struct A <: AbstractA

end
function __bytes__(self::A)::OtherBytesSubclass
return OtherBytesSubclass(b"abc")
end

assertEqual(self, bytes(A()), b"abc")
assertIs(self, type_(bytes(A())), OtherBytesSubclass)
assertEqual(self, BytesSubclass(A()), b"abc")
assertIs(self, type_(BytesSubclass(A())), BytesSubclass)
end

function test_from_format(self::BytesTest)
ctypes = import_module(import_helper, "ctypes")
_testcapi = import_module(import_helper, "_testcapi")
PyBytes_FromFormat = pythonapi.PyBytes_FromFormat
PyBytes_FromFormat.argtypes = (c_char_p,)
PyBytes_FromFormat.restype = py_object
@test (PyBytes_FromFormat(b"format") == b"format")
@test (PyBytes_FromFormat(b"Hello %s !", b"world") == b"Hello world !")
@test (PyBytes_FromFormat(b"c=%c", c_int(0)) == b"c=\x00")
@test (PyBytes_FromFormat(b"c=%c", c_int(ord("@"))) == b"c=@")
@test (PyBytes_FromFormat(b"c=%c", c_int(255)) == b"c=\xff")
@test (PyBytes_FromFormat(b"d=%d ld=%ld zd=%zd", c_int(1), c_long(2), c_size_t(3)) == b"d=1 ld=2 zd=3")
@test (PyBytes_FromFormat(b"d=%d ld=%ld zd=%zd", c_int(-1), c_long(-2), c_size_t(-3)) == b"d=-1 ld=-2 zd=-3")
@test (PyBytes_FromFormat(b"u=%u lu=%lu zu=%zu", c_uint(123), c_ulong(456), c_size_t(789)) == b"u=123 lu=456 zu=789")
@test (PyBytes_FromFormat(b"i=%i", c_int(123)) == b"i=123")
@test (PyBytes_FromFormat(b"i=%i", c_int(-123)) == b"i=-123")
@test (PyBytes_FromFormat(b"x=%x", c_int(2748)) == b"x=abc")
sizeof_ptr = sizeof(ctypes, c_char_p)
if os.name == "nt"
ptr_format = "0x%0$()X"
function ptr_formatter(ptr)::Any
return ptr_format % ptr
end

else
function ptr_formatter(ptr)::String
return "%#x" % ptr
end

end
ptr = 11259375
@test (PyBytes_FromFormat(b"ptr=%p", c_char_p(ptr)) == Vector{UInt8}("ptr=" + ptr_formatter(ptr)))
@test (PyBytes_FromFormat(b"s=%s", c_char_p(b"cstr")) == b"s=cstr")
size_max = c_size_t(-1).value
for (formatstr, ctypes_type, value, py_formatter) in ((b"%d", c_int, _testcapi.INT_MIN, str), (b"%d", c_int, _testcapi.INT_MAX, str), (b"%ld", c_long, _testcapi.LONG_MIN, str), (b"%ld", c_long, _testcapi.LONG_MAX, str), (b"%lu", c_ulong, _testcapi.ULONG_MAX, str), (b"%zd", c_ssize_t, _testcapi.PY_SSIZE_T_MIN, str), (b"%zd", c_ssize_t, _testcapi.PY_SSIZE_T_MAX, str), (b"%zu", c_size_t, size_max, str), (b"%p", c_char_p, size_max, ptr_formatter))
(@test (PyBytes_FromFormat(formatstr, ctypes_type(value)) == Vector{UInt8}(py_formatter(value))),)
end
@test (PyBytes_FromFormat(b"%5s", b"a") == b"a")
@test (PyBytes_FromFormat(b"%.3s", b"abcdef") == b"abc")
@test (PyBytes_FromFormat(b"%%") == b"%")
@test (PyBytes_FromFormat(b"[%%]") == b"[%]")
@test (PyBytes_FromFormat(b"%%%c", c_int(ord("_"))) == b"%_")
@test (PyBytes_FromFormat(b"%%s") == b"%s")
@test (PyBytes_FromFormat(b"%") == b"%")
@test (PyBytes_FromFormat(b"x=%i y=%", c_int(2), c_int(3)) == b"x=2 y=%")
@test_throws OverflowError PyBytes_FromFormat(b"%c", c_int(-1))
@test_throws OverflowError PyBytes_FromFormat(b"%c", c_int(256))
@test (PyBytes_FromFormat(b"") == b"")
@test (PyBytes_FromFormat(b"%s", b"") == b"")
end

function test_bytes_blocking(self::BufferBlocked)
mutable struct IterationBlocked <: AbstractIterationBlocked
__bytes__

                    IterationBlocked(__bytes__ = nothing) =
                        new(__bytes__)
end

i = [0, 1, 2, 3]
assertEqual(self, bytes(i), b"\x00\x01\x02\x03")
assertRaises(self, TypeError, bytes, IterationBlocked(i))
mutable struct IntBlocked <: AbstractIntBlocked
__bytes__

                    IntBlocked(__bytes__ = nothing) =
                        new(__bytes__)
end

assertEqual(self, bytes(3), b"\x00\x00\x00")
assertRaises(self, TypeError, bytes, IntBlocked(3))
mutable struct BytesSubclassBlocked <: AbstractBytesSubclassBlocked
__bytes__

                    BytesSubclassBlocked(__bytes__ = nothing) =
                        new(__bytes__)
end

assertEqual(self, bytes(b"ab"), b"ab")
assertRaises(self, TypeError, bytes, BytesSubclassBlocked(b"ab"))
mutable struct BufferBlocked <: AbstractBufferBlocked
__bytes__

                    BufferBlocked(__bytes__ = nothing) =
                        new(__bytes__)
end

ba, bb = (Vector{UInt8}(b"ab"), BufferBlocked(b"ab"))
assertEqual(self, bytes(ba), b"ab")
assertRaises(self, TypeError, bytes, bb)
end

function test_repeat_id_preserving(self::SubBytes)
a = b"123abc1@"
b = b"456zyx-+"
assertEqual(self, id(a), id(a))
assertNotEqual(self, id(a), id(b))
assertNotEqual(self, id(a), id(repeat(a,-4)))
assertNotEqual(self, id(a), id(repeat(a,0)))
assertEqual(self, id(a), id(repeat(a,1)))
assertEqual(self, id(a), id(repeat(a,1)))
assertNotEqual(self, id(a), id(repeat(a,2)))
mutable struct SubBytes <: AbstractSubBytes

end

s = SubBytes(b"qwerty()")
assertEqual(self, id(s), id(s))
assertNotEqual(self, id(s), id(__mul__(s, -4)))
assertNotEqual(self, id(s), id(__mul__(s, 0)))
assertNotEqual(self, id(s), id(__mul__(s, 1)))
assertNotEqual(self, id(s), id(__mul__(1, s)))
assertNotEqual(self, id(s), id(__mul__(s, 2)))
end

mutable struct ByteArrayTest <: AbstractByteArrayTest
test_exhausted_iterator
type2test

                    ByteArrayTest(test_exhausted_iterator = test.list_tests.CommonTest.test_exhausted_iterator, type2test = bytearray) =
                        new(test_exhausted_iterator, type2test)
end
function test_getitem_error(self::ByteArrayTest)
b = Vector{UInt8}(b"python")
msg = "bytearray indices must be integers or slices"
assertRaisesRegex(self, TypeError, msg) do 
b["a"]
end
end

function test_setitem_error(self::ByteArrayTest)
b = Vector{UInt8}(b"python")
msg = "bytearray indices must be integers or slices"
assertRaisesRegex(self, TypeError, msg) do 
b["a"] = "python"
end
end

function test_nohash(self::ByteArrayTest)
@test_throws TypeError hash(Vector{UInt8}())
end

function test_bytearray_api(self::ByteArrayTest)
short_sample = b"Hello world\n"
sample = append!(short_sample, repeat(b"\x00",(20 - length(short_sample))))
tfn = mktemp(tempfile)
try
readline(tfn) do f 
write(f, short_sample)
end
readline(tfn) do f 
b = Vector{UInt8}(20)
n = readinto(f, b)
end
@test (n == length(short_sample))
@test (collect(b) == collect(sample))
readline(tfn) do f 
write(f, b)
end
readline(tfn) do f 
@test (read(f) == sample)
end
finally
try
remove(os, tfn)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_reverse(self::ByteArrayTest)
b = Vector{UInt8}(b"hello")
@test (reverse(b) == nothing)
@test (b == b"olleh")
b = Vector{UInt8}(b"hello1")
reverse(b)
@test (b == b"1olleh")
b = Vector{UInt8}()
reverse(b)
@test !(b)
end

function test_clear(self::ByteArrayTest)
b = Vector{UInt8}(b"python")
clear(b)
@test (b == b"")
b = Vector{UInt8}(b"")
clear(b)
@test (b == b"")
b = Vector{UInt8}(b"")
append(b, ord("r"))
clear(b)
append(b, ord("p"))
@test (b == b"p")
end

function test_copy(self::ByteArrayTest)
b = Vector{UInt8}(b"abc")
bb = copy(b)
@test (bb == b"abc")
b = Vector{UInt8}(b"")
bb = copy(b)
@test (bb == b"")
b = Vector{UInt8}(b"abc")
bb = copy(b)
@test (b == bb)
assertIsNot(self, b, bb)
append(bb, ord("d"))
@test (bb == b"abcd")
@test (b == b"abc")
end

function test_regexps(self::ByteArrayTest)
function by(s)::Vector{Int8}
return Vector{UInt8}(map(ord, s))
end

b = by("Hello, world")
@test (findall(b"\\w+", b) == [by("Hello"), by("world")])
end

function test_setitem(self::ByteArrayTest)
b = Vector{UInt8}([1, 2, 3])
b[2] = 100
@test (b == Vector{UInt8}([1, 100, 3]))
b[end] = 200
@test (b == Vector{UInt8}([1, 100, 200]))
b[1] = Indexable(10)
@test (b == Vector{UInt8}([10, 100, 200]))
try
b[4] = 0
fail(self, "Didn\'t raise IndexError")
catch exn
if exn isa IndexError
#= pass =#
end
end
try
b[end - -8] = 0
fail(self, "Didn\'t raise IndexError")
catch exn
if exn isa IndexError
#= pass =#
end
end
try
b[1] = 256
fail(self, "Didn\'t raise ValueError")
catch exn
if exn isa ValueError
#= pass =#
end
end
try
b[1] = Indexable(-1)
fail(self, "Didn\'t raise ValueError")
catch exn
if exn isa ValueError
#= pass =#
end
end
try
b[1] = nothing
fail(self, "Didn\'t raise TypeError")
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function test_delitem(self::ByteArrayTest)
b = Vector{UInt8}(0:9)
#Delete Unsupported
del(b)
@test (b == Vector{UInt8}(1:9))
#Delete Unsupported
del(b)
@test (b == Vector{UInt8}(1:8))
#Delete Unsupported
del(b)
@test (b == Vector{UInt8}([1, 2, 3, 4, 6, 7, 8]))
end

function test_setslice(self::ByteArrayTest)
b = Vector{UInt8}(0:9)
@test (collect(b) == collect(0:9))
b[1:5] = Vector{UInt8}([1, 1, 1, 1, 1])
@test (b == Vector{UInt8}([1, 1, 1, 1, 1, 5, 6, 7, 8, 9]))
#Delete Unsupported
del(b)
@test (b == Vector{UInt8}([5, 6, 7, 8, 9]))
b[1:0] = Vector{UInt8}([0, 1, 2, 3, 4])
@test (b == Vector{UInt8}(0:9))
b[length(b) - -6:-3] = Vector{UInt8}([100, 101])
@test (b == Vector{UInt8}([0, 1, 2, 100, 101, 7, 8, 9]))
b[4:5] = [3, 4, 5, 6]
@test (b == Vector{UInt8}(0:9))
b[4:0] = [42, 42, 42]
@test (b == Vector{UInt8}([0, 1, 2, 42, 42, 42, 3, 4, 5, 6, 7, 8, 9]))
b[4:end] = b"foo"
@test (b == Vector{UInt8}([0, 1, 2, 102, 111, 111]))
b[begin:3] = memoryview(b"foo")
@test (b == Vector{UInt8}([102, 111, 111, 102, 111, 111]))
b[4:4] = []
@test (b == Vector{UInt8}([102, 111, 111, 111, 111]))
for elem in [5, -5, 0, Int(floor(1e+21)), "str", 2.3, ["a", "b"], [b"a", b"b"], [[]]]
assertRaises(self, TypeError) do 
b[4:4] = elem
end
end
for elem in [[254, 255, 256], [-256, 9000]]
assertRaises(self, ValueError) do 
b[4:4] = elem
end
end
end

function test_setslice_extend(self::ByteArrayTest)
b = Vector{UInt8}(0:99)
@test (collect(b) == collect(0:99))
#Delete Unsupported
del(b)
@test (collect(b) == collect(10:99))
extend(b, 100:109)
@test (collect(b) == collect(10:109))
end

function test_fifo_overrun(self::ByteArrayTest)
b = Vector{UInt8}(10)
pop(b)
#Delete Unsupported
del(b)
b += bytes(2)
#Delete Unsupported
del(b)
end

function test_del_expand(self::ByteArrayTest)
b = Vector{UInt8}(10)
size = getsizeof(sys, b)
#Delete Unsupported
del(b)
assertLessEqual(self, getsizeof(sys, b), size)
end

function test_extended_set_del_slice(self::ByteArrayTest)
indices = (0, nothing, 1, 3, 19, 300, 1 << 333, sys.maxsize, -1, -2, -31, -300)
for start in indices
for stop in indices
for step in indices[2:end]
L = collect(0:254)
b = Vector{UInt8}(L)
data = L[stop:step:start + 1]
reverse(data)
L[stop:step:start + 1] = data
b[stop:step:start + 1] = data
@test (b == Vector{UInt8}(L))
#Delete Unsupported
del(L)
#Delete Unsupported
del(b)
@test (b == Vector{UInt8}(L))
end
end
end
end

function test_setslice_trap(self::ByteArrayTest)
b = Vector{UInt8}(0:255)
b[9:end] = b
@test (b == Vector{UInt8}(append!(collect(0:7), collect(0:255))))
end

function test_iconcat(self::ByteArrayTest)
b = Vector{UInt8}(b"abc")
b1 = b
b += b"def"
@test (b == b"abcdef")
@test (b == b1)
assertIs(self, b, b1)
b += b"xyz"
@test (b == b"abcdefxyz")
try
b += ""
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function test_irepeat(self::ByteArrayTest)
b = Vector{UInt8}(b"abc")
b1 = b
b *= 3
@test (b == b"abcabcabc")
@test (b == b1)
assertIs(self, b, b1)
end

function test_irepeat_1char(self::ByteArrayTest)
b = Vector{UInt8}(b"x")
b1 = b
b *= 100
@test (b == repeat(b"x",100))
@test (b == b1)
assertIs(self, b, b1)
end

function test_alloc(self::ByteArrayTest)
b = Vector{UInt8}()
alloc = __alloc__(b)
assertGreaterEqual(self, alloc, 0)
seq = [alloc]
for i in 0:99
b += b"x"
alloc = __alloc__(b)
assertGreater(self, alloc, length(b))
if alloc ∉ seq
push!(seq, alloc)
end
end
end

function test_init_alloc(self::ByteArrayTest)
b = Vector{UInt8}()
function g()
Channel() do ch_g 
for i in 1:99
put!(ch_g, i)
a = collect(b)
@test (a == collect(1:length(a)))
@test (length(b) == length(a))
assertLessEqual(self, length(b), i)
alloc = __alloc__(b)
assertGreater(self, alloc, length(b))
end
end
end

__init__(b, g())
@test (collect(b) == collect(1:99))
@test (length(b) == 99)
alloc = __alloc__(b)
assertGreater(self, alloc, length(b))
end

function test_extend(self::ByteArrayTest)
orig = b"hello"
a = Vector{UInt8}(orig)
extend(a, a)
@test (a == append!(orig, orig))
@test (a[6:end] == orig)
a = Vector{UInt8}(b"")
extend(a, map(int, repeat(orig,25)))
extend(a, (parse(Int, x) for x in repeat(orig,25)))
@test (a == repeat(orig,50))
@test (a[length(a) - -4:end] == orig)
a = Vector{UInt8}(b"")
extend(a, (x for x in map(int, repeat(orig,50))))
@test (a == repeat(orig,50))
@test (a[length(a) - -4:end] == orig)
a = Vector{UInt8}(b"")
extend(a, collect(map(int, repeat(orig,50))))
@test (a == repeat(orig,50))
@test (a[length(a) - -4:end] == orig)
a = Vector{UInt8}(b"")
@test_throws ValueError a.extend([0, 1, 2, 256])
@test_throws ValueError a.extend([0, 1, 2, -1])
@test (length(a) == 0)
a = Vector{UInt8}(b"")
extend(a, [Indexable(ord("a"))])
@test (a == b"a")
end

function test_remove(self::ByteArrayTest)
b = Vector{UInt8}(b"hello")
remove(b, ord("l"))
@test (b == b"helo")
remove(b, ord("l"))
@test (b == b"heo")
@test_throws ValueError () -> remove(b, ord("l"))()
@test_throws ValueError () -> remove(b, 400)()
@test_throws TypeError () -> remove(b, "e")()
remove(b, ord("o"))
remove(b, ord("h"))
@test (b == b"e")
@test_throws TypeError () -> remove(b, b"e")()
remove(b, Indexable(ord("e")))
@test (b == b"")
c = Vector{UInt8}([126, 127, 128, 129])
remove(c, 127)
@test (c == bytes([126, 128, 129]))
remove(c, 129)
@test (c == bytes([126, 128]))
end

function test_pop(self::ByteArrayTest)
b = Vector{UInt8}(b"world")
@test (pop(b) == ord("d"))
@test (pop(b, 0) == ord("w"))
@test (pop(b, -2) == ord("r"))
@test_throws IndexError () -> pop(b, 10)()
@test_throws IndexError () -> pop(Vector{UInt8}())()
@test (pop(Vector{UInt8}(b"\xff")) == 255)
end

function test_nosort(self::ByteArrayTest)
@test_throws AttributeError () -> sort(Vector{UInt8}())()
end

function test_append(self::ByteArrayTest)
b = Vector{UInt8}(b"hell")
append(b, ord("o"))
@test (b == b"hello")
@test (append(b, 100) == nothing)
b = Vector{UInt8}()
append(b, ord("A"))
@test (length(b) == 1)
@test_throws TypeError () -> append(b, b"o")()
b = Vector{UInt8}()
append(b, Indexable(ord("A")))
@test (b == b"A")
end

function test_insert(self::ByteArrayTest)
b = Vector{UInt8}(b"msssspp")
insert(b, 1, ord("i"))
insert(b, 4, ord("i"))
insert(b, -2, ord("i"))
insert(b, 1000, ord("i"))
@test (b == b"mississippi")
@test_throws TypeError () -> insert(b, 0, b"1")()
b = Vector{UInt8}()
insert(b, 0, Indexable(ord("A")))
@test (b == b"A")
end

function test_copied(self::ByteArrayTest)
b = Vector{UInt8}(b"abc")
assertIsNot(self, b, replace(b, b"abc", b"cde", 0))
t = Vector{UInt8}([i for i in 0:255])
x = Vector{UInt8}(b"")
assertIsNot(self, x, translate(x, t))
end

function test_partition_bytearray_doesnt_share_nullstring(self::ByteArrayTest)
a, b, c = partition(Vector{UInt8}(b"x"), b"y")
@test (b == b"")
@test (c == b"")
assertIsNot(self, b, c)
b += b"!"
@test (c == b"")
a, b, c = partition(Vector{UInt8}(b"x"), b"y")
@test (b == b"")
@test (c == b"")
b, c, a = rpartition(Vector{UInt8}(b"x"), b"y")
@test (b == b"")
@test (c == b"")
assertIsNot(self, b, c)
b += b"!"
@test (c == b"")
c, b, a = rpartition(Vector{UInt8}(b"x"), b"y")
@test (b == b"")
@test (c == b"")
end

function test_resize_forbidden(self::ByteArrayTest)
b = Vector{UInt8}(0:9)
v = memoryview(b)
function resize(n)
b[2:-1] = n + 1:2*n - 2
end

resize(10)
orig = b[begin:end]
@test_throws BufferError resize(11)
@test (b == orig)
@test_throws BufferError resize(9)
@test (b == orig)
@test_throws BufferError resize(0)
@test (b == orig)
@test_throws BufferError b.pop(0)
@test (b == orig)
@test_throws BufferError b.remove(b[2])
@test (b == orig)
function delitem()
#Delete Unsupported
del(b)
end

@test_throws BufferError delitem()
@test (b == orig)
function delslice()
b[-1:2:2] = b""
end

@test_throws BufferError delslice()
@test (b == orig)
end

function test_obsolete_write_lock(self::ByteArrayTest)
@test_throws BufferError getbuffer_with_null_view(Vector{UInt8}())
end

function test_iterator_pickling2(self::ByteArrayTest)
orig = Vector{UInt8}(b"abc")
data = collect(b"qwerty")
for proto in 0:pickle.HIGHEST_PROTOCOL
itorig = (x for x in orig)
d = dumps(pickle, (itorig, orig), proto)
it, b = loads(pickle, d)
b[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data)
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, b = loads(pickle, d)
b[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[2:end])
for i in 1:length(orig) - 1
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, b = loads(pickle, d)
b[begin:end] = data
@test (type_(it) == type_(itorig))
@test (collect(it) == data[length(orig) + 1:end])
@test_throws StopIteration next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, b = loads(pickle, d)
b[begin:end] = data
@test (collect(it) == [])
end
end

function test_iterator_length_hint(self::ByteArrayTest)
ba = Vector{UInt8}(b"ab")
it = (x for x in ba)
next(it)
clear(ba)
@test (collect(it) == [])
end

function test_repeat_after_setslice(self::ByteArrayTest)
b = Vector{UInt8}(b"abc")
b[begin:2] = b"x"
b1 = repeat(b,1)
b3 = repeat(b,3)
@test (b1 == b"xc")
@test (b1 == b)
@test (b3 == b"xcxcxc")
end

mutable struct AssortedBytesTest <: AbstractAssortedBytesTest

end
function test_repr_str(self::AssortedBytesTest)
for f in (str, repr)
@test (f(Vector{UInt8}()) == "bytearray(b\'\')")
@test (f(Vector{UInt8}([0])) == "bytearray(b\'\\x00\')")
@test (f(Vector{UInt8}([0, 1, 254, 255])) == "bytearray(b\'\\x00\\x01\\xfe\\xff\')")
@test (f(b"abc") == "b\'abc\'")
@test (f(b"'") == "b\"\'\"")
@test (f(b"\'\"") == "b\'\\\'\"\'")
end
end

function test_format(self::AssortedBytesTest)
for b in (b"abc", Vector{UInt8}(b"abc"))
@test (b == string(b))
@test (b == string(b))
assertRaisesRegex(self, TypeError, "\\b%s\\b" % escape(re, type_(b).__name__)) do 
b
end
end
end

function test_compare_bytes_to_bytearray(self::AssortedBytesTest)
@test (b"abc" == bytes(b"abc") == true_)
@test (b"ab" != bytes(b"abc") == true_)
@test (b"ab" <= bytes(b"abc") == true_)
@test (b"ab" < bytes(b"abc") == true_)
@test (b"abc" >= bytes(b"ab") == true_)
@test (b"abc" > bytes(b"ab") == true_)
@test (b"abc" != bytes(b"abc") == false_)
@test (b"ab" == bytes(b"abc") == false_)
@test (b"ab" > bytes(b"abc") == false_)
@test (b"ab" >= bytes(b"abc") == false_)
@test (b"abc" < bytes(b"ab") == false_)
@test (b"abc" <= bytes(b"ab") == false_)
@test (bytes(b"abc") == b"abc" == true_)
@test (bytes(b"ab") != b"abc" == true_)
@test (bytes(b"ab") <= b"abc" == true_)
@test (bytes(b"ab") < b"abc" == true_)
@test (bytes(b"abc") >= b"ab" == true_)
@test (bytes(b"abc") > b"ab" == true_)
@test (bytes(b"abc") != b"abc" == false_)
@test (bytes(b"ab") == b"abc" == false_)
@test (bytes(b"ab") > b"abc" == false_)
@test (bytes(b"ab") >= b"abc" == false_)
@test (bytes(b"abc") < b"ab" == false_)
@test (bytes(b"abc") <= b"ab" == false_)
end

function test_doc(self::AssortedBytesTest)
assertIsNotNone(self, bytearray.__doc__)
@test startswith(bytearray.__doc__, "bytearray(")
assertIsNotNone(self, bytes.__doc__)
@test startswith(bytes.__doc__, "bytes(")
end

function test_from_bytearray(self::AssortedBytesTest)
sample = bytes(b"Hello world\n\x80\x81\xfe\xff")
buf = memoryview(sample)
b = Vector{UInt8}(buf)
@test (b == Vector{UInt8}(sample))
end

function test_to_str(self::AssortedBytesTest)
@test (string(b"") == "b\'\'")
@test (string(b"x") == "b\'x\'")
@test (string(b"\x80") == "b\'\\x80\'")
@test (string(Vector{UInt8}(b"")) == "bytearray(b\'\')")
@test (string(Vector{UInt8}(b"x")) == "bytearray(b\'x\')")
@test (string(Vector{UInt8}(b"\x80")) == "bytearray(b\'\\x80\')")
end

function test_literal(self::AssortedBytesTest)
tests = [(b"Wonderful spam", "Wonderful spam"), (b"Wonderful spam too", "Wonderful spam too"), (b"\xaa\x00\x00\x80", "ª  "), (b"\\xaa\\x00\\000\\200", "\\xaa\\x00\\000\\200")]
for (b, s) in tests
@test (b == Vector{UInt8}(s))
end
for c in 128:255
@test_throws SyntaxError eval("b\"%s\"" % chr(c))
end
end

function test_split_bytearray(self::AssortedBytesTest)
@test (split(b"a b", memoryview(b" ")) == [b"a", b"b"])
end

function test_rsplit_bytearray(self::AssortedBytesTest)
@test (rsplit(b"a b", memoryview(b" ")) == [b"a", b"b"])
end

function test_return_self(self::AssortedBytesTest)
b = Vector{UInt8}()
assertIsNot(self, replace(b, b"", b""), b)
end

function test_compare(self::AssortedBytesTest)
function bytes_warning()
return check_warnings(warnings_helper, ("", BytesWarning))
end

bytes_warning() do 
b"" == ""
end
bytes_warning() do 
"" == b""
end
bytes_warning() do 
b"" != ""
end
bytes_warning() do 
"" != b""
end
bytes_warning() do 
Vector{UInt8}(b"") == ""
end
bytes_warning() do 
"" == Vector{UInt8}(b"")
end
bytes_warning() do 
Vector{UInt8}(b"") != ""
end
bytes_warning() do 
"" != Vector{UInt8}(b"")
end
bytes_warning() do 
b"\x00" == 0
end
bytes_warning() do 
0 == b"\x00"
end
bytes_warning() do 
b"\x00" != 0
end
bytes_warning() do 
0 != b"\x00"
end
end

mutable struct BytearrayPEP3137Test <: AbstractBytearrayPEP3137Test

end
function marshal(self::BytearrayPEP3137Test, x)::Vector{Int8}
return Vector{UInt8}(x)
end

function test_returns_new_copy(self::BytearrayPEP3137Test)
val = marshal(self, b"1234")
for methname in ("zfill", "rjust", "ljust", "center")
method = getfield(val, methname
newval = method(3)
@test (val == newval)
assertIsNot(self, val, newval, methname + " returned self on a mutable object")
end
for expr in ("val.split()[0]", "val.rsplit()[0]", "val.partition(b\".\")[0]", "val.rpartition(b\".\")[2]", "val.splitlines()[0]", "val.replace(b\"\", b\"\")")
newval = eval(expr)
@test (val == newval)
assertIsNot(self, val, newval, expr + " returned val on a mutable object")
end
sep = marshal(self, b"")
newval = join([val], sep)
@test (val == newval)
assertIsNot(self, val, newval)
end

mutable struct FixedStringTest <: AbstractFixedStringTest
contains_bytes::Bool

                    FixedStringTest(contains_bytes::Bool = true) =
                        new(contains_bytes)
end
function fixtype(self::FixedStringTest, obj)
if isa(obj, str)
return type2test(self, Vector{UInt8}(obj))
end
return fixtype(super(), obj)
end

mutable struct ByteArrayAsStringTest <: AbstractByteArrayAsStringTest
type2test

                    ByteArrayAsStringTest(type2test = bytearray) =
                        new(type2test)
end

mutable struct BytesAsStringTest <: AbstractBytesAsStringTest
type2test

                    BytesAsStringTest(type2test = bytes) =
                        new(type2test)
end

mutable struct SubclassTest <: AbstractSubclassTest
type2test
basetype
end
function test_basic(self::SubclassTest)
assertTrue(self, self.type2test <: self.basetype)
assertIsInstance(self, type2test(self), self.basetype)
a, b = (b"abcd", b"efgh")
_a, _b = (type2test(self, a), type2test(self, b))
assertTrue(self, _a === _a)
assertTrue(self, _a != _b)
assertTrue(self, _a < _b)
assertTrue(self, _a <= _b)
assertTrue(self, _b >= _a)
assertTrue(self, _b > _a)
assertIsNot(self, _a, a)
assertEqual(self, a + b, _a + _b)
assertEqual(self, a + b, a + _b)
assertEqual(self, a + b, _a + b)
assertTrue(self, (a*5) == (_a*5))
end

function test_join(self::SubclassTest)
s1 = type2test(self, b"abcd")
s2 = join([s1], basetype(self))
assertIsNot(self, s1, s2)
assertIs(self, type_(s2), self.basetype, type_(s2))
s3 = join([b"abcd"], s1)
assertIs(self, type_(s3), self.basetype)
end

function test_pickle(self::SubclassTest)
a = type2test(self, b"abcd")
a.x = 10
a.y = type2test(self, b"efgh")
for proto in 0:pickle.HIGHEST_PROTOCOL
b = loads(pickle, dumps(pickle, a, proto))
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
assertEqual(self, a.x, b.x)
assertEqual(self, a.y, b.y)
assertEqual(self, type_(a), type_(b))
assertEqual(self, type_(a.y), type_(b.y))
end
end

function test_copy(self::SubclassTest)
a = type2test(self, b"abcd")
a.x = 10
a.y = type2test(self, b"efgh")
for copy_method in (copy.copy, copy.deepcopy)
b = copy_method(a)
assertNotEqual(self, id(a), id(b))
assertEqual(self, a, b)
assertEqual(self, a.x, b.x)
assertEqual(self, a.y, b.y)
assertEqual(self, type_(a), type_(b))
assertEqual(self, type_(a.y), type_(b.y))
end
end

function test_fromhex(self::B2)
b = fromhex(self.type2test, "1a2B30")
assertEqual(self, b, b"\x1a+0")
assertIs(self, type_(b), self.type2test)
mutable struct B1 <: AbstractB1
basetype
end
function __new__(cls, value)
me = __new__(self.basetype, cls)
me.foo = "bar"
return me
end

b = fromhex(B1, "1a2B30")
assertEqual(self, b, b"\x1a+0")
assertIs(self, type_(b), B1)
assertEqual(self, b.foo, "bar")
mutable struct B2 <: AbstractB2
basetype

            B2() = begin
                if basetype != bytes
basetype.__init__(me, args..., kwargs)
end
                new()
            end
end

b = fromhex(B2, "1a2B30")
assertEqual(self, b, b"\x1a+0")
assertIs(self, type_(b), B2)
assertEqual(self, b.foo, "bar")
end

mutable struct ByteArraySubclass <: AbstractByteArraySubclass

end

mutable struct BytesSubclass <: AbstractBytesSubclass

end

mutable struct OtherBytesSubclass <: AbstractOtherBytesSubclass

end

mutable struct ByteArraySubclassTest <: AbstractByteArraySubclassTest
basetype
newarg::Int64
type2test::AbstractByteArraySubclass

                    ByteArraySubclassTest(basetype = bytearray, newarg::Int64 = 1, type2test::AbstractByteArraySubclass = ByteArraySubclass) =
                        new(basetype, newarg, type2test)
end
function test_init_override(self::subclass)
mutable struct subclass <: Abstractsubclass
newarg::Int64

            subclass(newarg = 1) = begin
                bytearray.__init__(me, args..., kwargs)
                new(newarg )
            end
end

x = subclass(4, b"abcd")
x = subclass(4, b"abcd")
assertEqual(self, x, b"abcd")
x = subclass(4, b"abcd")
assertEqual(self, x, b"abcd")
end

mutable struct BytesSubclassTest <: AbstractBytesSubclassTest
basetype
type2test::AbstractBytesSubclass

                    BytesSubclassTest(basetype = bytes, type2test::AbstractBytesSubclass = BytesSubclass) =
                        new(basetype, type2test)
end

function main()
bytes_test = BytesTest()
test_getitem_error(bytes_test)
test_buffer_is_readonly(bytes_test)
test_custom(bytes_test)
test_from_format(bytes_test)
test_bytes_blocking(bytes_test)
test_repeat_id_preserving(bytes_test)
byte_array_test = ByteArrayTest()
test_getitem_error(byte_array_test)
test_setitem_error(byte_array_test)
test_nohash(byte_array_test)
test_bytearray_api(byte_array_test)
test_reverse(byte_array_test)
test_clear(byte_array_test)
test_copy(byte_array_test)
test_regexps(byte_array_test)
test_setitem(byte_array_test)
test_delitem(byte_array_test)
test_setslice(byte_array_test)
test_setslice_extend(byte_array_test)
test_fifo_overrun(byte_array_test)
test_del_expand(byte_array_test)
test_extended_set_del_slice(byte_array_test)
test_setslice_trap(byte_array_test)
test_iconcat(byte_array_test)
test_irepeat(byte_array_test)
test_irepeat_1char(byte_array_test)
test_alloc(byte_array_test)
test_init_alloc(byte_array_test)
test_extend(byte_array_test)
test_remove(byte_array_test)
test_pop(byte_array_test)
test_nosort(byte_array_test)
test_append(byte_array_test)
test_insert(byte_array_test)
test_copied(byte_array_test)
test_partition_bytearray_doesnt_share_nullstring(byte_array_test)
test_resize_forbidden(byte_array_test)
test_obsolete_write_lock(byte_array_test)
test_iterator_pickling2(byte_array_test)
test_iterator_length_hint(byte_array_test)
test_repeat_after_setslice(byte_array_test)
assorted_bytes_test = AssortedBytesTest()
test_repr_str(assorted_bytes_test)
test_format(assorted_bytes_test)
test_compare_bytes_to_bytearray(assorted_bytes_test)
test_doc(assorted_bytes_test)
test_from_bytearray(assorted_bytes_test)
test_to_str(assorted_bytes_test)
test_literal(assorted_bytes_test)
test_split_bytearray(assorted_bytes_test)
test_rsplit_bytearray(assorted_bytes_test)
test_return_self(assorted_bytes_test)
test_compare(assorted_bytes_test)
bytearray_p_e_p3137_test = BytearrayPEP3137Test()
marshal(bytearray_p_e_p3137_test)
test_returns_new_copy(bytearray_p_e_p3137_test)
byte_array_as_string_test = ByteArrayAsStringTest()
bytes_as_string_test = BytesAsStringTest()
byte_array_subclass_test = ByteArraySubclassTest()
test_init_override(byte_array_subclass_test)
bytes_subclass_test = BytesSubclassTest()
end

main()