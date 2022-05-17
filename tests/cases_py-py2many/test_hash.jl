using PyCall
using Test
datetime = pyimport("datetime")




using test.support.script_helper: assert_python_ok
using collections.abc: Hashable
abstract type AbstractHashEqualityTestCase end
abstract type AbstractDefaultHash <: Abstractobject end
abstract type AbstractFixedHash <: Abstractobject end
abstract type AbstractOnlyEquality <: Abstractobject end
abstract type AbstractOnlyInequality <: Abstractobject end
abstract type AbstractInheritedHashWithEquality <: AbstractFixedHash end
abstract type AbstractInheritedHashWithInequality <: AbstractFixedHash end
abstract type AbstractNoHash <: Abstractobject end
abstract type AbstractHashInheritanceTestCase end
abstract type AbstractDefaultIterSeq <: Abstractobject end
abstract type AbstractHashBuiltinsTestCase end
abstract type AbstractHashRandomizationTests end
abstract type AbstractStringlikeHashRandomizationTests <: AbstractHashRandomizationTests end
abstract type AbstractStrHashRandomizationTests <: AbstractStringlikeHashRandomizationTests end
abstract type AbstractBytesHashRandomizationTests <: AbstractStringlikeHashRandomizationTests end
abstract type AbstractMemoryviewHashRandomizationTests <: AbstractStringlikeHashRandomizationTests end
abstract type AbstractDatetimeTests <: AbstractHashRandomizationTests end
abstract type AbstractDatetimeDateTests <: AbstractDatetimeTests end
abstract type AbstractDatetimeDatetimeTests <: AbstractDatetimeTests end
abstract type AbstractDatetimeTimeTests <: AbstractDatetimeTests end
abstract type AbstractHashDistributionTestCase end
IS_64BIT = sys.maxsize > (2^32)
function lcg(x, length = 16)::Array{UInt8}
#= Linear congruential generator =#
if x == 0
return bytes(length)
end
out = Vector{UInt8}(length)
for i in 0:length - 1
x = (214013*x + 2531011) & 2147483647
out[i + 1] = (x >> 16) & 255
end
return bytes(out)
end

function pysiphash(uint64)::Tuple
#= Convert SipHash24 output to Py_hash_t
     =#
@assert(0 <= uint64 < (1 << 64))
if uint64 > ((1 << 63) - 1)
int64 = uint64 - (1 << 64)
else
int64 = uint64
end
uint32 = (uint64  ⊻  (uint64 >> 32)) & 4294967295
if uint32 > ((1 << 31) - 1)
int32 = uint32 - (1 << 32)
else
int32 = uint32
end
return (int32, int64)
end

function skip_unless_internalhash(test)
#= Skip decorator for tests that depend on SipHash24 or FNV =#
ok = sys.hash_info.algorithm ∈ Set(["fnv", "siphash24"])
msg = "Requires SipHash24 or FNV"
return ok ? (test) : (skip(unittest, msg)(test))
end

mutable struct HashEqualityTestCase <: AbstractHashEqualityTestCase

end
function same_hash(self::HashEqualityTestCase)
hashed = collect(map(hash, objlist))
for h in hashed[2:end]
if h != hashed[1]
fail(self, "hashed values differ: %r" % (objlist,))
end
end
end

function test_numeric_literals(self::HashEqualityTestCase)
same_hash(self)
same_hash(self)
same_hash(self)
same_hash(self)
end

function test_coerced_integers(self::HashEqualityTestCase)
same_hash(self)
same_hash(self)
same_hash(self)
same_hash(self)
same_hash(self)
same_hash(self)
same_hash(self)
end

function test_coerced_floats(self::HashEqualityTestCase)
same_hash(self)
same_hash(self)
end

function test_unaligned_buffers(self::HashEqualityTestCase)
b = repeat(b"123456789abcdefghijklmnopqrstuvwxyz",128)
for i in 0:15
for j in 0:15
aligned = b[i + 1:128 + j]
unaligned = memoryview(b)[i + 1:128 + j]
@test (hash(aligned) == hash(unaligned))
end
end
end

_default_hash = object.__hash__
mutable struct DefaultHash <: AbstractDefaultHash

end

_FIXED_HASH_VALUE = 42
mutable struct FixedHash <: AbstractFixedHash

end
function __hash__(self::FixedHash)::Int64
return _FIXED_HASH_VALUE
end

mutable struct OnlyEquality <: AbstractOnlyEquality

end
function __eq__(self::OnlyEquality, other)::Bool
return self == other
end

mutable struct OnlyInequality <: AbstractOnlyInequality

end
function __ne__(self::OnlyInequality, other)::Bool
return self != other
end

mutable struct InheritedHashWithEquality <: AbstractInheritedHashWithEquality

end

mutable struct InheritedHashWithInequality <: AbstractInheritedHashWithInequality

end

mutable struct NoHash <: AbstractNoHash
__hash__

                    NoHash(__hash__ = nothing) =
                        new(__hash__)
end

mutable struct HashInheritanceTestCase <: AbstractHashInheritanceTestCase
default_expected::Vector{Union{DefaultHash, OnlyInequality}}
error_expected::Vector{Union{NoHash, OnlyEquality}}
fixed_expected::Vector{Union{InheritedHashWithEquality, FixedHash, InheritedHashWithInequality}}

                    HashInheritanceTestCase(default_expected::Vector{Union{DefaultHash, OnlyInequality}} = [object(), DefaultHash(), OnlyInequality()], error_expected::Vector{Union{NoHash, OnlyEquality}} = [NoHash(), OnlyEquality()], fixed_expected::Vector{Union{InheritedHashWithEquality, FixedHash, InheritedHashWithInequality}} = [FixedHash(), InheritedHashWithEquality(), InheritedHashWithInequality()]) =
                        new(default_expected, error_expected, fixed_expected)
end
function test_default_hash(self::HashInheritanceTestCase)
for obj in self.default_expected
@test (hash(obj) == _default_hash(obj))
end
end

function test_fixed_hash(self::HashInheritanceTestCase)
for obj in self.fixed_expected
@test (hash(obj) == _FIXED_HASH_VALUE)
end
end

function test_error_hash(self::HashInheritanceTestCase)
for obj in self.error_expected
@test_throws TypeError hash(obj)
end
end

function test_hashable(self::HashInheritanceTestCase)
objects = self.default_expected + self.fixed_expected
for obj in objects
@test isa(self, obj)
end
end

function test_not_hashable(self::HashInheritanceTestCase)
for obj in self.error_expected
assertNotIsInstance(self, obj, Hashable)
end
end

mutable struct DefaultIterSeq <: AbstractDefaultIterSeq
seq

                    DefaultIterSeq(seq = 0:9) =
                        new(seq)
end
function __len__(self::DefaultIterSeq)::Int64
return length(self.seq)
end

function __getitem__(self::DefaultIterSeq, index)
return self.seq[index + 1]
end

mutable struct HashBuiltinsTestCase <: AbstractHashBuiltinsTestCase
hashes_to_check::Vector

                    HashBuiltinsTestCase(hashes_to_check::Vector = [enumerate(0:9), (x for x in DefaultIterSeq()), (x for x in () -> 0)]) =
                        new(hashes_to_check)
end
function test_hashes(self::HashBuiltinsTestCase)
_default_hash = object.__hash__
for obj in self.hashes_to_check
@test (hash(obj) == _default_hash(obj))
end
end

mutable struct HashRandomizationTests <: AbstractHashRandomizationTests

end
function get_hash_command(self::HashRandomizationTests, repr_)::String
return "print(hash(eval(%a)))" % repr_
end

function get_hash(self::HashRandomizationTests, repr_, seed = nothing)::Int64
env = copy(os.environ)
env["__cleanenv"] = true
if seed != nothing
env["PYTHONHASHSEED"] = string(seed)
else
pop(env, "PYTHONHASHSEED", nothing)
end
out = assert_python_ok("-c", get_hash_command(self, repr_), env)
stdout = strip(out[2])
return parse(Int, stdout)
end

function test_randomized_hash(self::HashRandomizationTests)
run1 = get_hash(self, self.repr_)
run2 = get_hash(self, self.repr_)
assertNotEqual(self, run1, run2)
end

mutable struct StringlikeHashRandomizationTests <: AbstractStringlikeHashRandomizationTests
known_hashes::Dict{String, Vector{Vector{Int64}}}
repr_
repr_long

                    StringlikeHashRandomizationTests(known_hashes::Dict{String, Vector{Vector{Int64}}} = Dict("djba33x" => [[193485960, 193485960, 193485960, 193485960], [-678966196, 573763426263223372, -820489388, -4282905804826039665]], "siphash24" => [[1198583518, 4596069200710135518, 1198583518, 4596069200710135518], [273876886, -4501618152524544106, 273876886, -4501618152524544106], [-1745215313, 4436719588892876975, -1745215313, 4436719588892876975], [493570806, 5749986484189612790, -1006381564, -5915111450199468540], [-1677110816, -2947981342227738144, -1860207793, -4296699217652516017]], "fnv" => [[-1600925533, 1453079729188098211, -1600925533, 1453079729188098211], [-206076799, -4410911502303878509, -1024014457, -3570150969479994130], [811136751, -5046230049376118746, -77208053, -4779029615281019666], [44402817, 8998297579845987431, -1956240331, -782697888614047887], [-283066365, -4576729883824601543, -271871407, -3927695501187247084]]), repr_ = nothing, repr_long = nothing) =
                        new(known_hashes, repr_, repr_long)
end
function get_expected_hash(self::StringlikeHashRandomizationTests, position, length)::List<List<int>>
if length < sys.hash_info.cutoff
algorithm = "djba33x"
else
algorithm = sys.hash_info.algorithm
end
if sys.byteorder == "little"
platform = IS_64BIT ? (1) : (0)
else
@assert(sys.byteorder == "big")
platform = IS_64BIT ? (3) : (2)
end
return self.known_hashes[algorithm][position][platform]
end

function test_null_hash(self::StringlikeHashRandomizationTests)
known_hash_of_obj = get_expected_hash(self, 0, 3)
assertNotEqual(self, get_hash(self, self.repr_), known_hash_of_obj)
assertEqual(self, get_hash(self, self.repr_, 0), known_hash_of_obj)
end

function test_fixed_hash(self::StringlikeHashRandomizationTests)
h = get_expected_hash(self, 1, 3)
assertEqual(self, get_hash(self, self.repr_, 42), h)
end

function test_long_fixed_hash(self::StringlikeHashRandomizationTests)
if self.repr_long === nothing
return
end
h = get_expected_hash(self, 2, 11)
assertEqual(self, get_hash(self, self.repr_long, 42), h)
end

mutable struct StrHashRandomizationTests <: AbstractStrHashRandomizationTests
repr_
repr_long
repr_ucs2

                    StrHashRandomizationTests(repr_ = repr("abc"), repr_long = repr("abcdefghijk"), repr_ucs2 = repr("äú∑ℇ")) =
                        new(repr_, repr_long, repr_ucs2)
end
function test_empty_string(self::StrHashRandomizationTests)
@test (hash("") == 0)
end

function test_ucs2_string(self::StrHashRandomizationTests)
h = get_expected_hash(self, 3, 6)
@test (get_hash(self, self.repr_ucs2, 0) == h)
h = get_expected_hash(self, 4, 6)
@test (get_hash(self, self.repr_ucs2, 42) == h)
end

mutable struct BytesHashRandomizationTests <: AbstractBytesHashRandomizationTests
repr_
repr_long

                    BytesHashRandomizationTests(repr_ = repr(b"abc"), repr_long = repr(b"abcdefghijk")) =
                        new(repr_, repr_long)
end
function test_empty_string(self::BytesHashRandomizationTests)
@test (hash(b"") == 0)
end

mutable struct MemoryviewHashRandomizationTests <: AbstractMemoryviewHashRandomizationTests
repr_::String
repr_long::String

                    MemoryviewHashRandomizationTests(repr_::String = "memoryview(b\'abc\')", repr_long::String = "memoryview(b\'abcdefghijk\')") =
                        new(repr_, repr_long)
end
function test_empty_string(self::MemoryviewHashRandomizationTests)
@test (hash(memoryview(b"")) == 0)
end

mutable struct DatetimeTests <: AbstractDatetimeTests

end
function get_hash_command(self::DatetimeTests, repr_)::String
return "import datetime; print(hash(%s))" % repr_
end

mutable struct DatetimeDateTests <: AbstractDatetimeDateTests
repr_

                    DatetimeDateTests(repr_ = repr(date(datetime, 1066, 10, 14))) =
                        new(repr_)
end

mutable struct DatetimeDatetimeTests <: AbstractDatetimeDatetimeTests
repr_

                    DatetimeDatetimeTests(repr_ = repr(datetime(datetime, 1, 2, 3, 4, 5, 6, 7))) =
                        new(repr_)
end

mutable struct DatetimeTimeTests <: AbstractDatetimeTimeTests
repr_

                    DatetimeTimeTests(repr_ = repr(time(datetime, 0))) =
                        new(repr_)
end

mutable struct HashDistributionTestCase <: AbstractHashDistributionTestCase

end
function test_hash_distribution(self::HashDistributionTestCase)
base = "abcdefghabcdefg"
for i in 1:length(base) - 1
prefix = base[begin:i]
subTest(self, prefix) do 
s15 = set()
s255 = set()
for c in 0:255
h = hash(prefix + chr(c))
add(s15, h & 15)
add(s255, h & 255)
end
assertGreater(self, length(s15), 8, prefix)
assertGreater(self, length(s255), 128, prefix)
end
end
end

function main()
hash_equality_test_case = HashEqualityTestCase()
same_hash(hash_equality_test_case)
test_numeric_literals(hash_equality_test_case)
test_coerced_integers(hash_equality_test_case)
test_coerced_floats(hash_equality_test_case)
test_unaligned_buffers(hash_equality_test_case)
hash_inheritance_test_case = HashInheritanceTestCase()
test_default_hash(hash_inheritance_test_case)
test_fixed_hash(hash_inheritance_test_case)
test_error_hash(hash_inheritance_test_case)
test_hashable(hash_inheritance_test_case)
test_not_hashable(hash_inheritance_test_case)
hash_builtins_test_case = HashBuiltinsTestCase()
test_hashes(hash_builtins_test_case)
str_hash_randomization_tests = StrHashRandomizationTests()
test_empty_string(str_hash_randomization_tests)
test_ucs2_string(str_hash_randomization_tests)
bytes_hash_randomization_tests = BytesHashRandomizationTests()
test_empty_string(bytes_hash_randomization_tests)
memoryview_hash_randomization_tests = MemoryviewHashRandomizationTests()
test_empty_string(memoryview_hash_randomization_tests)
datetime_date_tests = DatetimeDateTests()
datetime_datetime_tests = DatetimeDatetimeTests()
datetime_time_tests = DatetimeTimeTests()
hash_distribution_test_case = HashDistributionTestCase()
test_hash_distribution(hash_distribution_test_case)
end

main()