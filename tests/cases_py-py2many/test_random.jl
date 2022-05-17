using Test
import _random



import random



import warnings

using functools: partial


using fractions: Fraction

mutable struct TestBasicOps <: AbstractTestBasicOps
_items
gen
end
function randomlist(self::TestBasicOps, n)
#= Helper function to make a list of random numbers =#
return [random(self.gen) for i in 0:n - 1]
end

function test_autoseed(self::TestBasicOps)
seed(self.gen)
state1 = getstate(self.gen)
sleep(time, 0.1)
seed(self.gen)
state2 = getstate(self.gen)
assertNotEqual(self, state1, state2)
end

function test_saverestore(self::TestBasicOps)
N = 1000
seed(self.gen)
state = getstate(self.gen)
randseq = randomlist(self, N)
setstate(self.gen, state)
assertEqual(self, randseq, randomlist(self, N))
end

function test_seedargs(self::MySeed)
mutable struct MySeed <: AbstractMySeed

end
function __hash__(self::MySeed)::Int64
return -1729
end

for arg in [nothing, 0, 1, -1, 10^20, -(10^20), false, true, 3.14, "a"]
seed(self.gen, arg)
end
for arg in [1 + 2im, tuple("abc"), MySeed()]
assertWarns(self, DeprecationWarning) do 
seed(self.gen, arg)
end
end
for arg in [collect(0:2), dict(1)]
assertWarns(self, DeprecationWarning) do 
assertRaises(self, TypeError, self.gen.seed, arg)
end
end
assertRaises(self, TypeError, self.gen.seed, 1, 2, 3, 4)
assertRaises(self, TypeError, type_(self.gen), [])
end

function test_seed_no_mutate_bug_44018(self::TestBasicOps)
a = Vector{UInt8}(b"1234")
seed(self.gen, a)
assertEqual(self, a, Vector{UInt8}(b"1234"))
end

function test_seed_when_randomness_source_not_found(self::TestBasicOps, urandom_mock)
urandom_mock.side_effect = NotImplementedError
test_seedargs(self)
end

function test_shuffle(self::TestBasicOps)
shuffle = self.gen.shuffle
lst = []
shuffle(lst)
assertEqual(self, lst, [])
lst = [37]
shuffle(lst)
assertEqual(self, lst, [37])
seqs = [collect(0:n - 1) for n in 0:9]
shuffled_seqs = [collect(0:n - 1) for n in 0:9]
for shuffled_seq in shuffled_seqs
shuffle(shuffled_seq)
end
for (seq, shuffled_seq) in zip(seqs, shuffled_seqs)
assertEqual(self, length(seq), length(shuffled_seq))
assertEqual(self, set(seq), set(shuffled_seq))
end
lst = collect(0:999)
shuffled_lst = collect(0:999)
shuffle(shuffled_lst)
assertTrue(self, lst != shuffled_lst)
shuffle(lst)
assertTrue(self, lst != shuffled_lst)
assertRaises(self, TypeError, shuffle, (1, 2, 3))
end

function test_shuffle_random_argument(self::TestBasicOps)
shuffle = self.gen.shuffle
mock_random = Mock(unittest.mock, 0.5)
seq = Vector{UInt8}(b"abcdefghijk")
assertWarns(self, DeprecationWarning) do 
shuffle(seq, mock_random)
end
assert_called_with(mock_random)
end

function test_choice(self::TestBasicOps)
choice = self.gen.choice
assertRaises(self, IndexError) do 
choice([])
end
assertEqual(self, choice([50]), 50)
assertIn(self, choice([25, 75]), [25, 75])
end

function test_sample(self::TestBasicOps)
N = 100
population = 0:N - 1
for k in 0:N
s = sample(self.gen, population, k)
assertEqual(self, length(s), k)
uniq = set(s)
assertEqual(self, length(uniq), k)
assertTrue(self, uniq <= set(population))
end
assertEqual(self, sample(self.gen, [], 0), [])
assertRaises(self, ValueError, self.gen.sample, population, N + 1)
assertRaises(self, ValueError, self.gen.sample, [], -1)
end

function test_sample_distribution(self::TestBasicOps)
n = 5
pop = 0:n - 1
trials = 10000
for k in 0:n - 1
expected = factorial(n) ÷ factorial(n - k)
perms = Dict()
for i in 0:trials - 1
perms[tuple(sample(self.gen, pop, k))] = nothing
if length(perms) == expected
break;
end
end
end
end

function test_sample_inputs(self::TestBasicOps)
sample(self.gen, 0:19, 2)
sample(self.gen, 0:19, 2)
sample(self.gen, string("abcdefghijklmnopqrst"), 2)
sample(self.gen, tuple("abcdefghijklmnopqrst"), 2)
end

function test_sample_on_dicts(self::TestBasicOps)
assertRaises(self, TypeError, self.gen.sample, fromkeys(dict, "abcdef"), 2)
end

function test_sample_on_sets(self::TestBasicOps)
assertWarns(self, DeprecationWarning) do 
population = Set([10, 20, 30, 40, 50, 60, 70])
sample(self.gen, population, 5)
end
end

function test_sample_on_seqsets(self::SeqSet)
mutable struct SeqSet <: abc.Sequence
_items
end
function __len__(self::SeqSet)::Int64
return length(self._items)
end

function __getitem__(self::SeqSet, index)
return self._items[index + 1]
end

population = SeqSet([2, 4, 1, 3])
catch_warnings(warnings) do 
simplefilter(warnings, "error", DeprecationWarning)
sample(self.gen, population, 2)
end
end

function test_sample_with_counts(self::TestBasicOps)
sample = self.gen.sample
colors = ["red", "green", "blue", "orange", "black", "brown", "amber"]
counts = [500, 200, 20, 10, 5, 0, 1]
k = 700
summary = Counter(sample(colors, counts, k))
assertEqual(self, sum(values(summary)), k)
for (color, weight) in zip(colors, counts)
assertLessEqual(self, summary[color + 1], weight)
end
assertNotIn(self, "brown", summary)
k = sum(counts)
summary = Counter(sample(colors, counts, k))
assertEqual(self, sum(values(summary)), k)
for (color, weight) in zip(colors, counts)
assertLessEqual(self, summary[color + 1], weight)
end
assertNotIn(self, "brown", summary)
summary = Counter(sample(["x"], [10], 8))
assertEqual(self, summary, Counter(8))
nc = length(colors)
summary = Counter(sample(colors, repeat([10],nc), 10*nc))
assertEqual(self, summary, Counter(repeat(colors,10)))
assertRaises(self, TypeError) do 
sample(["red", "green", "blue"], 10, 10)
end
assertRaises(self, ValueError) do 
sample(["red", "green", "blue"], [-3, -7, -8], 2)
end
assertRaises(self, ValueError) do 
sample(["red", "green", "blue"], [0, 0, 0], 2)
end
assertRaises(self, ValueError) do 
sample(["red", "green"], [10, 10], 21)
end
assertRaises(self, ValueError) do 
sample(["red", "green", "blue"], [1, 2], 2)
end
assertRaises(self, ValueError) do 
sample(["red", "green", "blue"], [1, 2, 3, 4], 2)
end
end

function test_choices(self::TestBasicOps)
choices = self.gen.choices
data = ["red", "green", "blue", "yellow"]
str_data = "abcd"
range_data = 0:3
set_data = set(0:3)
for sample in [choices(data, 5), choices(data, 0:3, 5), choices(5, data, 0:3), choices(5, data, 0:3)]
assertEqual(self, length(sample), 5)
assertEqual(self, type_(sample), list)
assertTrue(self, set(sample) <= set(data))
end
assertRaises(self, TypeError) do 
choices(2)
end
assertEqual(self, choices(data, 0), [])
assertEqual(self, choices(data, -1), [])
assertRaises(self, TypeError) do 
choices(data, 2.5)
end
assertTrue(self, set(choices(str_data, 5)) <= set(str_data))
assertTrue(self, set(choices(range_data, 5)) <= set(range_data))
assertRaises(self, TypeError) do 
choices(set_data, 2)
end
assertTrue(self, set(choices(data, nothing, 5)) <= set(data))
assertTrue(self, set(choices(data, nothing, 5)) <= set(data))
assertRaises(self, ValueError) do 
choices(data, [1, 2], 5)
end
assertRaises(self, TypeError) do 
choices(data, 10, 5)
end
assertRaises(self, TypeError) do 
choices(data, repeat([nothing],4), 5)
end
for weights in [[15, 10, 25, 30], [15.1, 10.2, 25.2, 30.3], [Fraction(1, 3), Fraction(2, 6), Fraction(3, 6), Fraction(4, 6)], [true, false, true, false]]
assertTrue(self, set(choices(data, weights, 5)) <= set(data))
end
assertRaises(self, ValueError) do 
choices(data, [1, 2], 5)
end
assertRaises(self, TypeError) do 
choices(data, 10, 5)
end
assertRaises(self, TypeError) do 
choices(data, repeat([nothing],4), 5)
end
assertRaises(self, TypeError) do 
choices(data, 0:3, 0:3, 5)
end
for weights in [[15, 10, 25, 30], [15.1, 10.2, 25.2, 30.3], [Fraction(1, 3), Fraction(2, 6), Fraction(3, 6), Fraction(4, 6)]]
assertTrue(self, set(choices(data, weights, 5)) <= set(data))
end
assertEqual(self, choices("abcd", [1, 0, 0, 0]), ["a"])
assertEqual(self, choices("abcd", [0, 1, 0, 0]), ["b"])
assertEqual(self, choices("abcd", [0, 0, 1, 0]), ["c"])
assertEqual(self, choices("abcd", [0, 0, 0, 1]), ["d"])
assertRaises(self, IndexError) do 
choices([], 1)
end
assertRaises(self, IndexError) do 
choices([], [], 1)
end
assertRaises(self, IndexError) do 
choices([], [], 5)
end
end

function test_choices_subnormal(self::TestBasicOps)
choices = self.gen.choices
choices([1, 2], [1e-323, 1e-323], 5000)
end

function test_choices_with_all_zero_weights(self::TestBasicOps)
assertRaises(self, ValueError) do 
choices(self.gen, "AB", [0.0, 0.0])
end
end

function test_choices_negative_total(self::TestBasicOps)
assertRaises(self, ValueError) do 
choices(self.gen, "ABC", [3, -5, 1])
end
end

function test_choices_infinite_total(self::TestBasicOps)
assertRaises(self, ValueError) do 
choices(self.gen, "A", [float("inf")])
end
assertRaises(self, ValueError) do 
choices(self.gen, "AB", [0.0, float("inf")])
end
assertRaises(self, ValueError) do 
choices(self.gen, "AB", [-float("inf"), 123])
end
assertRaises(self, ValueError) do 
choices(self.gen, "AB", [0.0, float("nan")])
end
assertRaises(self, ValueError) do 
choices(self.gen, "AB", [float("-inf"), float("inf")])
end
end

function test_gauss(self::TestBasicOps)
for seed in (1, 12, 123, 1234, 12345, 123456, 654321)
seed(self.gen, seed)
x1 = random(self.gen)
y1 = gauss(self.gen, 0, 1)
seed(self.gen, seed)
x2 = random(self.gen)
y2 = gauss(self.gen, 0, 1)
assertEqual(self, x1, x2)
assertEqual(self, y1, y2)
end
end

function test_getrandbits(self::TestBasicOps)
for k in 1:999
assertTrue(self, 0 <= getrandbits(self.gen, k) < (2^k))
end
assertEqual(self, getrandbits(self.gen, 0), 0)
getbits = self.gen.getrandbits
for span in [1, 2, 3, 4, 31, 32, 32, 52, 53, 54, 119, 127, 128, 129]
all_bits = 2^span - 1
cum = 0
cpl_cum = 0
for i in 0:99
v = getbits(span)
cum |= v
cpl_cum |= all_bits  ⊻  v
end
assertEqual(self, cum, all_bits)
assertEqual(self, cpl_cum, all_bits)
end
assertRaises(self, TypeError, self.gen.getrandbits)
assertRaises(self, TypeError, self.gen.getrandbits, 1, 2)
assertRaises(self, ValueError, self.gen.getrandbits, -1)
assertRaises(self, TypeError, self.gen.getrandbits, 10.1)
end

function test_pickling(self::TestBasicOps)
for proto in 0:pickle.HIGHEST_PROTOCOL
state = dumps(pickle, self.gen, proto)
origseq = [random(self.gen) for i in 0:9]
newgen = loads(pickle, state)
restoredseq = [random(newgen) for i in 0:9]
assertEqual(self, origseq, restoredseq)
end
end

function test_bug_41052(self::TestBasicOps)
for proto in 0:pickle.HIGHEST_PROTOCOL
r = Random(_random)
assertRaises(self, TypeError, pickle.dumps, r, proto)
end
end

function test_bug_42008(self::TestBasicOps)
r1 = Random(_random)
seed(r1, 8675309)
r2 = Random(_random, 8675309)
assertEqual(self, random(r1), random(r2))
end

function test_bug_1727780(self::TestBasicOps)
files = [("randv2_32.pck", 780), ("randv2_64.pck", 866), ("randv3.pck", 343)]
for (file, value) in files
readline(findfile(support, file)) do f 
r = load(pickle, f)
end
assertEqual(self, Int(random(r)*1000), value)
end
end

function test_bug_9025(self::TestBasicOps)
n = 100000
randrange = self.gen.randrange
k = sum(((randrange(6755399441055744) % 3) == 2 for i in 0:n - 1))
assertTrue(self, 0.3 < (k / n) < 0.37, k / n)
end

function test_randbytes(self::TestBasicOps)
for n in 1:9
data = randbytes(self.gen, n)
assertEqual(self, type_(data), bytes)
assertEqual(self, length(data), n)
end
assertEqual(self, randbytes(self.gen, 0), b"")
assertRaises(self, TypeError, self.gen.randbytes)
assertRaises(self, TypeError, self.gen.randbytes, 1, 2)
assertRaises(self, ValueError, self.gen.randbytes, -1)
assertRaises(self, TypeError, self.gen.randbytes, 1.0)
end

abstract type AbstractTestBasicOps end
abstract type AbstractMySeed <: Abstractobject end
abstract type AbstractSeqSet <: Abstractabc.Sequence end
abstract type AbstractSystemRandom_TestBasicOps <: AbstractTestBasicOps end
abstract type AbstractMersenneTwister_TestBasicOps <: AbstractTestBasicOps end
abstract type AbstractBadInt <: Abstractint end
abstract type AbstractTestDistributions end
abstract type AbstractTestRandomSubclassing end
abstract type AbstractSubclass <: Abstractrandom.Random end
abstract type AbstractSubClass1 <: Abstractrandom.Random end
abstract type AbstractSubClass2 <: Abstractrandom.Random end
abstract type AbstractSubClass3 <: AbstractSubClass2 end
abstract type AbstractSubClass4 <: AbstractSubClass3 end
abstract type AbstractMixin1 end
abstract type AbstractMixin2 end
abstract type AbstractSubClass5 <: AbstractMixin1 end
abstract type AbstractSubClass6 <: AbstractMixin2 end
abstract type AbstractSubClass7 <: AbstractMixin1 end
abstract type AbstractSubClass8 <: AbstractMixin2 end
abstract type AbstractTestModule end
try
random(SystemRandom(random))
catch exn
if exn isa NotImplementedError
SystemRandom_available = false
end
end
mutable struct SystemRandom_TestBasicOps <: AbstractSystemRandom_TestBasicOps
gen

                    SystemRandom_TestBasicOps(gen = SystemRandom(random)) =
                        new(gen)
end
function test_autoseed(self::SystemRandom_TestBasicOps)
seed(self.gen)
end

function test_saverestore(self::SystemRandom_TestBasicOps)
@test_throws NotImplementedError self.gen.getstate()
@test_throws NotImplementedError self.gen.setstate(nothing)
end

function test_seedargs(self::SystemRandom_TestBasicOps)
seed(self.gen, 100)
end

function test_gauss(self::SystemRandom_TestBasicOps)
self.gen.gauss_next = nothing
seed(self.gen, 100)
@test (self.gen.gauss_next == nothing)
end

function test_pickling(self::SystemRandom_TestBasicOps)
for proto in 0:pickle.HIGHEST_PROTOCOL
@test_throws NotImplementedError pickle.dumps(self.gen, proto)
end
end

function test_53_bits_per_float(self::SystemRandom_TestBasicOps)
span = 2^53
cum = 0
for i in 0:99
cum |= Int(random(self.gen)*span)
end
@test (cum == span - 1)
end

function test_bigrand(self::SystemRandom_TestBasicOps)
span = 2^500
cum = 0
for i in 0:99
r = randrange(self.gen, span)
@test 0 <= r < span
cum |= r
end
@test (cum == span - 1)
end

function test_bigrand_ranges(self::SystemRandom_TestBasicOps)
for i in [40, 80, 160, 200, 211, 250, 375, 512, 550]
start = randrange(self.gen, 2^(i - 2))
stop = randrange(self.gen, 2^i)
if stop <= start
continue;
end
@test start <= randrange(self.gen, start, stop) < stop
end
end

function test_rangelimits(self::SystemRandom_TestBasicOps)
for (start, stop) in [(-2, 0), (-(2^60) - 2, -(2^60)), (2^60, 2^60 + 2)]
@test (set(start:stop - 1) == set([randrange(self.gen, start, stop) for i in 0:99]))
end
end

function test_randrange_nonunit_step(self::SystemRandom_TestBasicOps)
rint = randrange(self.gen, 0, 10, 2)
assertIn(self, rint, (0, 2, 4, 6, 8))
rint = randrange(self.gen, 0, 2, 2)
@test (rint == 0)
end

function test_randrange_errors(self::SystemRandom_TestBasicOps)
raises = partial(self.assertRaises, ValueError, self.gen.randrange)
raises(3, 3)
raises(-721)
raises(0, 100, -12)
assertWarns(self, DeprecationWarning, raises, 3.14159)
assertWarns(self, DeprecationWarning, self.gen.randrange, 3.0)
assertWarns(self, DeprecationWarning, self.gen.randrange, Fraction(3, 1))
assertWarns(self, DeprecationWarning, raises, "3")
assertWarns(self, DeprecationWarning, raises, 0, 2.71828)
assertWarns(self, DeprecationWarning, self.gen.randrange, 0, 2.0)
assertWarns(self, DeprecationWarning, self.gen.randrange, 0, Fraction(2, 1))
assertWarns(self, DeprecationWarning, raises, 0, "2")
raises(0, 42, 0)
assertWarns(self, DeprecationWarning, raises, 0, 42, 0.0)
assertWarns(self, DeprecationWarning, raises, 0, 0, 0.0)
assertWarns(self, DeprecationWarning, raises, 0, 42, 3.14159)
assertWarns(self, DeprecationWarning, self.gen.randrange, 0, 42, 3.0)
assertWarns(self, DeprecationWarning, self.gen.randrange, 0, 42, Fraction(3, 1))
assertWarns(self, DeprecationWarning, raises, 0, 42, "3")
assertWarns(self, DeprecationWarning, self.gen.randrange, 0, 42, 1.0)
assertWarns(self, DeprecationWarning, raises, 0, 0, 1.0)
end

function test_randrange_argument_handling(self::SystemRandom_TestBasicOps)
randrange = self.gen.randrange
assertWarns(self, DeprecationWarning) do 
randrange(10.0, 20, 2)
end
assertWarns(self, DeprecationWarning) do 
randrange(10, 20.0, 2)
end
assertWarns(self, DeprecationWarning) do 
randrange(10, 20, 1.0)
end
assertWarns(self, DeprecationWarning) do 
randrange(10, 20, 2.0)
end
assertWarns(self, DeprecationWarning) do 
assertRaises(self, ValueError) do 
randrange(10.5)
end
end
assertWarns(self, DeprecationWarning) do 
assertRaises(self, ValueError) do 
randrange(10, 20.5)
end
end
assertWarns(self, DeprecationWarning) do 
assertRaises(self, ValueError) do 
randrange(10, 20, 1.5)
end
end
end

function test_randrange_step(self::SystemRandom_TestBasicOps)
randrange = self.gen.randrange
assertRaises(self, TypeError) do 
randrange(1000, 100)
end
assertRaises(self, TypeError) do 
randrange(1000, nothing, 100)
end
end

function test_randbelow_logic(self::SystemRandom_TestBasicOps, _log = log, int = int)
for i in 1:999
n = 1 << i
numbits = i + 1
k = Int(floor(1.00001 + _log(n, 2)))
@test (k == numbits)
@test (n == 2^(k - 1))
n += n - 1
k = Int(floor(1.00001 + _log(n, 2)))
assertIn(self, k, [numbits, numbits + 1])
@test (2^k) > n > (2^(k - 2))
n -= n >> 15
k = Int(floor(1.00001 + _log(n, 2)))
@test (k == numbits)
@test (2^k) > n > (2^(k - 1))
end
end

mutable struct MersenneTwister_TestBasicOps <: AbstractMersenneTwister_TestBasicOps
gen

                    MersenneTwister_TestBasicOps(gen = Random(random)) =
                        new(gen)
end
function test_guaranteed_stable(self::MersenneTwister_TestBasicOps)
seed(self.gen, 3456147, 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.ac362300d90d2p-1", "0x1.9d16f74365005p-1", "0x1.1ebb4352e4c4dp-1", "0x1.1a7422abf9c11p-1"])
seed(self.gen, "the quick brown fox", 2)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.1239ddfb11b7cp-3", "0x1.b3cbb5c51b120p-4", "0x1.8c4f55116b60fp-1", "0x1.63eb525174a27p-1"])
end

function test_bug_27706(self::MersenneTwister_TestBasicOps)
seed(self.gen, "nofar", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.8645314505ad7p-1", "0x1.afb1f82e40a40p-5", "0x1.2a59d2285e971p-1", "0x1.56977142a7880p-6"])
seed(self.gen, "rachel", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.0b294cc856fcdp-1", "0x1.2ad22d79e77b8p-3", "0x1.3052b9c072678p-2", "0x1.578f332106574p-3"])
seed(self.gen, "", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.b0580f98a7dbep-1", "0x1.84129978f9c1ap-1", "0x1.aeaa51052e978p-2", "0x1.092178fb945a6p-2"])
end

function test_bug_31478(self::BadInt)
mutable struct BadInt <: AbstractBadInt

end
function __abs__(self::BadInt)
return nothing
end

try
seed(self.gen, BadInt())
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function test_bug_31482(self::MersenneTwister_TestBasicOps)
seed(self.gen, b"nofar", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.8645314505ad7p-1", "0x1.afb1f82e40a40p-5", "0x1.2a59d2285e971p-1", "0x1.56977142a7880p-6"])
seed(self.gen, b"rachel", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.0b294cc856fcdp-1", "0x1.2ad22d79e77b8p-3", "0x1.3052b9c072678p-2", "0x1.578f332106574p-3"])
seed(self.gen, b"", 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.b0580f98a7dbep-1", "0x1.84129978f9c1ap-1", "0x1.aeaa51052e978p-2", "0x1.092178fb945a6p-2"])
b = b"\x00 @`\x80\xa0\xc0\xe0\xf0"
seed(self.gen, b, 1)
@test ([hex(random(self.gen)) for i in 0:3] == ["0x1.52c2fde444d23p-1", "0x1.875174f0daea4p-2", "0x1.9e9b2c50e5cd2p-1", "0x1.fa57768bd321cp-2"])
end

function test_setstate_first_arg(self::MersenneTwister_TestBasicOps)
@test_throws ValueError self.gen.setstate((1, nothing, nothing))
end

function test_setstate_middle_arg(self::MersenneTwister_TestBasicOps)
start_state = getstate(self.gen)
@test_throws TypeError self.gen.setstate((2, nothing, nothing))
@test_throws ValueError self.gen.setstate((2, (1, 2, 3), nothing))
@test_throws TypeError self.gen.setstate((2, repeat([("a",)...],625), nothing))
@test_throws TypeError self.gen.setstate((2, repeat([(0,)...],624) + ("a",), nothing))
assertRaises(self, (ValueError, OverflowError)) do 
setstate(self.gen, (2, repeat([(1,)...],624) + (625,), nothing))
end
assertRaises(self, (ValueError, OverflowError)) do 
setstate(self.gen, (2, repeat([(1,)...],624) + (-1,), nothing))
end
bits100 = getrandbits(self.gen, 100)
setstate(self.gen, start_state)
@test (getrandbits(self.gen, 100) == bits100)
state_values = getstate(self.gen)[2]
state_values = collect(state_values)
state_values[end] = float("nan")
state = (parse(Int, x) for x in state_values)
@test_throws TypeError self.gen.setstate((2, state, nothing))
end

function test_referenceImplementation(self::MersenneTwister_TestBasicOps)
expected = [0.4583980307371326, 0.8605781520197878, 0.9284833172678215, 0.3593268111978246, 0.08182349376244957, 0.1433222647016933, 0.08429782382352002, 0.5381486467183145, 0.0892150249119934, 0.7848619610537291]
seed(self.gen, ((61731 + (24903 << 32)) + (614 << 64)) + (42143 << 96))
actual = randomlist(self, 2000)[length(randomlist(self, 2000)) - -9:end]
for (a, e) in zip(actual, expected)
assertAlmostEqual(self, a, e, 14)
end
end

function test_strong_reference_implementation(self::MersenneTwister_TestBasicOps)
expected = [4128882400830239, 7751398889519013, 8363034243334166, 3236528186029503, 737000512037440, 1290932195808883, 759287295919497, 4847212089661076, 803577505899006, 7069408070677702]
seed(self.gen, ((61731 + (24903 << 32)) + (614 << 64)) + (42143 << 96))
actual = randomlist(self, 2000)[length(randomlist(self, 2000)) - -9:end]
for (a, e) in zip(actual, expected)
@test (parse(Int, ldexp(a, 53)) == e)
end
end

function test_long_seed(self::MersenneTwister_TestBasicOps)
seed = (1 << 10000*8) - 1
seed(self.gen, seed)
end

function test_53_bits_per_float(self::MersenneTwister_TestBasicOps)
span = 2^53
cum = 0
for i in 0:99
cum |= Int(random(self.gen)*span)
end
@test (cum == span - 1)
end

function test_bigrand(self::MersenneTwister_TestBasicOps)
span = 2^500
cum = 0
for i in 0:99
r = randrange(self.gen, span)
@test 0 <= r < span
cum |= r
end
@test (cum == span - 1)
end

function test_bigrand_ranges(self::MersenneTwister_TestBasicOps)
for i in [40, 80, 160, 200, 211, 250, 375, 512, 550]
start = randrange(self.gen, 2^(i - 2))
stop = randrange(self.gen, 2^i)
if stop <= start
continue;
end
@test start <= randrange(self.gen, start, stop) < stop
end
end

function test_rangelimits(self::MersenneTwister_TestBasicOps)
for (start, stop) in [(-2, 0), (-(2^60) - 2, -(2^60)), (2^60, 2^60 + 2)]
@test (set(start:stop - 1) == set([randrange(self.gen, start, stop) for i in 0:99]))
end
end

function test_getrandbits(self::MersenneTwister_TestBasicOps)
test_getrandbits(super())
seed(self.gen, 1234567)
@test (getrandbits(self.gen, 100) == 97904845777343510404718956115)
end

function test_randrange_uses_getrandbits(self::MersenneTwister_TestBasicOps)
seed(self.gen, 1234567)
@test (randrange(self.gen, 2^99) == 97904845777343510404718956115)
end

function test_randbelow_logic(self::MersenneTwister_TestBasicOps, _log = log, int = int)
for i in 1:999
n = 1 << i
numbits = i + 1
k = Int(floor(1.00001 + _log(n, 2)))
@test (k == numbits)
@test (n == 2^(k - 1))
n += n - 1
k = Int(floor(1.00001 + _log(n, 2)))
assertIn(self, k, [numbits, numbits + 1])
@test (2^k) > n > (2^(k - 2))
n -= n >> 15
k = Int(floor(1.00001 + _log(n, 2)))
@test (k == numbits)
@test (2^k) > n > (2^(k - 1))
end
end

function test_randbelow_without_getrandbits(self::MersenneTwister_TestBasicOps)
maxsize = 1 << random.BPF
catch_warnings(warnings) do 
simplefilter(warnings, "ignore", UserWarning)
_randbelow_without_getrandbits(self.gen, maxsize + 1, maxsize)
end
_randbelow_without_getrandbits(self.gen, 5640, maxsize)
x = _randbelow_without_getrandbits(self.gen, 0, maxsize)
@test (x == 0)
n = 42
epsilon = 0.01
limit = (maxsize - (maxsize % n)) / maxsize
object(unittest.mock.patch, random.Random, "random") do random_mock 
random_mock.side_effect = [limit + epsilon, limit - epsilon]
_randbelow_without_getrandbits(self.gen, n, maxsize)
@test (random_mock.call_count == 2)
end
end

function test_randrange_bug_1590891(self::MersenneTwister_TestBasicOps)
start = 1000000000000
stop = -100000000000000000000
step = -200
x = randrange(self.gen, start, stop, step)
@test stop < x <= start
@test ((x + stop) % step == 0)
end

function test_choices_algorithms(self::MersenneTwister_TestBasicOps)
choices = self.gen.choices
n = 104729
seed(self.gen, 8675309)
a = choices(self.gen, 0:n - 1, 10000)
seed(self.gen, 8675309)
b = choices(self.gen, 0:n - 1, repeat([1],n), 10000)
@test (a == b)
seed(self.gen, 8675309)
c = choices(self.gen, 0:n - 1, 1:n, 10000)
@test (a == c)
population = ["Red", "Black", "Green"]
weights = [18, 18, 2]
cum_weights = [18, 36, 38]
expanded_population = append!(append!(repeat(["Red"],18), repeat(["Black"],18)), repeat(["Green"],2))
seed(self.gen, 9035768)
a = choices(self.gen, expanded_population, 10000)
seed(self.gen, 9035768)
b = choices(self.gen, population, weights, 10000)
@test (a == b)
seed(self.gen, 9035768)
c = choices(self.gen, population, cum_weights, 10000)
@test (a == c)
end

function test_randbytes(self::MersenneTwister_TestBasicOps)
test_randbytes(super())
seed = 8675309
expected = b"3\xa8\xf9f\xf4\xa4\xd06\x19\x8f\x9f\x82\x02oe\xf0"
seed(self.gen, seed)
@test (randbytes(self.gen, 16) == expected)
seed(self.gen, seed)
@test (randbytes(self.gen, 0) == b"")
@test (randbytes(self.gen, 16) == expected)
seed(self.gen, seed)
@test (join([randbytes(self.gen, 4) for _ in 0:3], b"") == expected)
seed(self.gen, seed)
expected1 = expected[end:4:4]
@test (join((randbytes(self.gen, 1) for _ in 0:3), b"") == expected1)
seed(self.gen, seed)
expected2 = join((expected[i + 3:i + 4] for i in 0:4:length(expected) - 1), b"")
@test (join((randbytes(self.gen, 2) for _ in 0:3), b"") == expected2)
seed(self.gen, seed)
expected3 = join((expected[i + 2:i + 4] for i in 0:4:length(expected) - 1), b"")
@test (join((randbytes(self.gen, 3) for _ in 0:3), b"") == expected3)
end

function test_randbytes_getrandbits(self::MersenneTwister_TestBasicOps)
seed = 2849427419
gen2 = Random(random)
seed(self.gen, seed)
seed(gen2, seed)
for n in 0:8
@test (randbytes(self.gen, n) == to_bytes(getrandbits(gen2, n*8), n, "little"))
end
end

function test_sample_counts_equivalence(self::MersenneTwister_TestBasicOps)
sample = self.gen.sample
seed = self.gen.seed
colors = ["red", "green", "blue", "orange", "black", "amber"]
counts = [500, 200, 20, 10, 5, 1]
k = 700
seed(8675309)
s1 = sample(colors, counts, k)
seed(8675309)
expanded = [color for (color, count) in zip(colors, counts) for i in 0:count - 1]
@test (length(expanded) == sum(counts))
s2 = sample(expanded, k)
@test (s1 == s2)
pop = "abcdefghi"
counts = [10, 9, 8, 7, 6, 5, 4, 3, 2]
seed(8675309)
s1 = join(sample(pop, counts, 30), "")
expanded = join([letter for (letter, count) in zip(pop, counts) for i in 0:count - 1], "")
seed(8675309)
s2 = join(sample(expanded, 30), "")
@test (s1 == s2)
end

function gamma(z, sqrt2pi = __mul__(2.0, pi)^0.5)::Union[Union[float,Any],float]
if z < 0.5
return __div__(pi, sin(__mul__(pi, z))) / gamma(1.0 - z)
end
az = z + (7.0 - 0.5)
return (az^(z - 0.5) / exp(az))*sqrt2pi*fsum([0.9999999999995183, 676.5203681218835 / z, -1259.139216722289 / (z + 1.0), 771.3234287757674 / (z + 2.0), -176.6150291498386 / (z + 3.0), 12.50734324009056 / (z + 4.0), -0.1385710331296526 / (z + 5.0), 9.934937113930748e-06 / (z + 6.0), 1.659470187408462e-07 / (z + 7.0)])
end

mutable struct TestDistributions <: AbstractTestDistributions

end
function test_zeroinputs(self::TestDistributions)
g = Random(random)
x = [random(g) for i in 0:49] + repeat([0.0],5)
g.random = x[begin:end].pop
uniform(g, 1, 10)
g.random = x[begin:end].pop
paretovariate(g, 1.0)
g.random = x[begin:end].pop
expovariate(g, 1.0)
g.random = x[begin:end].pop
weibullvariate(g, 1.0, 1.0)
g.random = x[begin:end].pop
vonmisesvariate(g, 1.0, 1.0)
g.random = x[begin:end].pop
normalvariate(g, 0.0, 1.0)
g.random = x[begin:end].pop
gauss(g, 0.0, 1.0)
g.random = x[begin:end].pop
lognormvariate(g, 0.0, 1.0)
g.random = x[begin:end].pop
vonmisesvariate(g, 0.0, 1.0)
g.random = x[begin:end].pop
gammavariate(g, 0.01, 1.0)
g.random = x[begin:end].pop
gammavariate(g, 1.0, 1.0)
g.random = x[begin:end].pop
gammavariate(g, 200.0, 1.0)
g.random = x[begin:end].pop
betavariate(g, 3.0, 3.0)
g.random = x[begin:end].pop
triangular(g, 0.0, 1.0, 1.0 / 3.0)
end

function test_avg_std(self::TestDistributions)
g = Random(random)
N = 5000
x = [i / float(N) for i in 1:N - 1]
for (variate, args, mu, sigmasqrd) in [(g.uniform, (1.0, 10.0), (10.0 + 1.0) / 2, (10.0 - 1.0)^2 / 12), (g.triangular, (0.0, 1.0, 1.0 / 3.0), 4.0 / 9.0, (7.0 / 9.0) / 18.0), (g.expovariate, (1.5,), 1 / 1.5, 1 / 1.5^2), (g.vonmisesvariate, (1.23, 0), pi, __pow__(pi, 2) / 3), (g.paretovariate, (5.0,), 5.0 / (5.0 - 1), 5.0 / (5.0 - 1)^2*(5.0 - 2)), (g.weibullvariate, (1.0, 3.0), gamma(1 + (1 / 3.0)), gamma(1 + (2 / 3.0)) - gamma(1 + (1 / 3.0))^2)]
g.random = x[begin:end].pop
y = []
for i in 0:length(x) - 1
try
push!(y, variate(args...))
catch exn
if exn isa IndexError
#= pass =#
end
end
end
s1 = 0
s2 = 0
for e in y
s1 += e
s2 += (e - mu)^2
end
N = length(y)
assertAlmostEqual(self, s1 / N, mu, 2, "%s%r" % (variate.__name__, args))
assertAlmostEqual(self, s2 / (N - 1), sigmasqrd, 2, "%s%r" % (variate.__name__, args))
end
end

function test_constant(self::TestDistributions)
g = Random(random)
N = 100
for (variate, args, expected) in [(g.uniform, (10.0, 10.0), 10.0), (g.triangular, (10.0, 10.0), 10.0), (g.triangular, (10.0, 10.0, 10.0), 10.0), (g.expovariate, (float("inf"),), 0.0), (g.vonmisesvariate, (3.0, float("inf")), 3.0), (g.gauss, (10.0, 0.0), 10.0), (g.lognormvariate, (0.0, 0.0), 1.0), (g.lognormvariate, (-float("inf"), 0.0), 0.0), (g.normalvariate, (10.0, 0.0), 10.0), (g.paretovariate, (float("inf"),), 1.0), (g.weibullvariate, (10.0, float("inf")), 10.0), (g.weibullvariate, (0.0, 10.0), 0.0)]
for i in 0:N - 1
@test (variate(args...) == expected)
end
end
end

function test_von_mises_range(self::TestDistributions)
g = Random(random)
N = 100
for mu in (0.0, 0.1, 3.1, 6.2)
for kappa in (0.0, 2.3, 500.0)
for _ in 0:N - 1
sample = vonmisesvariate(g, mu, kappa)
@test 0 <= sample <= random.TWOPI
end
end
end
end

function test_von_mises_large_kappa(self::TestDistributions)
vonmisesvariate(random, 0, 1000000000000000.0)
vonmisesvariate(random, 0, 1e+100)
end

function test_gammavariate_errors(self::TestDistributions)
@test_throws ValueError random.gammavariate(-1, 3)
@test_throws ValueError random.gammavariate(0, 2)
@test_throws ValueError random.gammavariate(2, 0)
@test_throws ValueError random.gammavariate(1, -3)
end

function test_gammavariate_alpha_greater_one(self::TestDistributions, random_mock)
random_mock.side_effect = [1e-08, 0.5, 0.3]
returned_value = gammavariate(random, 1.1, 2.3)
assertAlmostEqual(self, returned_value, 2.53)
end

function test_gammavariate_alpha_equal_one(self::TestDistributions, random_mock)
random_mock.side_effect = [0.45]
returned_value = gammavariate(random, 1.0, 3.14)
assertAlmostEqual(self, returned_value, 1.877208182372648)
end

function test_gammavariate_alpha_equal_one_equals_expovariate(self::TestDistributions, random_mock)
beta = 3.14
random_mock.side_effect = [1e-08, 1e-08]
gammavariate_returned_value = gammavariate(random, 1.0, beta)
expovariate_returned_value = expovariate(random, 1.0 / beta)
assertAlmostEqual(self, gammavariate_returned_value, expovariate_returned_value)
end

function test_gammavariate_alpha_between_zero_and_one(self::TestDistributions, random_mock)
_e = random._e
_exp = random._exp
_log = random._log
alpha = 0.35
beta = 1.45
b = (_e + alpha) / _e
epsilon = 0.01
r1 = 0.8859296441566
r2 = 0.3678794411714
random_mock.side_effect = [r1, r2 + epsilon, r1, r2]
returned_value = gammavariate(random, alpha, beta)
assertAlmostEqual(self, returned_value, 1.4499999999997544)
r1 = 0.8959296441566
r2 = 0.9445400408898141
random_mock.side_effect = [r1, r2 + epsilon, r1, r2]
returned_value = gammavariate(random, alpha, beta)
assertAlmostEqual(self, returned_value, 1.5830349561760781)
end

function test_betavariate_return_zero(self::TestDistributions, gammavariate_mock)
gammavariate_mock.return_value = 0.0
@test (0.0 == betavariate(random, 2.71828, 3.14159))
end

mutable struct TestRandomSubclassing <: AbstractTestRandomSubclassing
newarg

                    TestRandomSubclassing(newarg = nothing) =
                        new(newarg)
end
function test_random_subclass_with_kwargs(self::Subclass)
mutable struct Subclass <: AbstractSubclass
newarg

            Subclass(newarg = nothing) = begin
                random.Random.__init__(self)
                new(newarg )
            end
end

Subclass(1)
end

function test_subclasses_overriding_methods(self::SubClass8)
mutable struct SubClass1 <: AbstractSubClass1

end
function random(self::SubClass1)
add(called, "SubClass1.random")
return random(random.Random)
end

function getrandbits(self::SubClass1, n)
add(called, "SubClass1.getrandbits")
return getrandbits(random.Random, self)
end

called = set()
randrange(SubClass1(), 42)
assertEqual(self, called, Set(["SubClass1.getrandbits"]))
mutable struct SubClass2 <: AbstractSubClass2

end
function random(self::SubClass2)
add(called, "SubClass2.random")
return random(random.Random)
end

called = set()
randrange(SubClass2(), 42)
assertEqual(self, called, Set(["SubClass2.random"]))
mutable struct SubClass3 <: AbstractSubClass3

end
function getrandbits(self::SubClass3, n)
add(called, "SubClass3.getrandbits")
return getrandbits(random.Random, self)
end

called = set()
randrange(SubClass3(), 42)
assertEqual(self, called, Set(["SubClass3.getrandbits"]))
mutable struct SubClass4 <: AbstractSubClass4

end
function random(self::SubClass4)
add(called, "SubClass4.random")
return random(random.Random)
end

called = set()
randrange(SubClass4(), 42)
assertEqual(self, called, Set(["SubClass4.random"]))
mutable struct Mixin1 <: AbstractMixin1

end
function random(self::Mixin1)
add(called, "Mixin1.random")
return random(random.Random)
end

mutable struct Mixin2 <: AbstractMixin2

end
function getrandbits(self::Mixin2, n)
add(called, "Mixin2.getrandbits")
return getrandbits(random.Random, self)
end

mutable struct SubClass5 <: AbstractSubClass5

end

called = set()
randrange(SubClass5(), 42)
assertEqual(self, called, Set(["Mixin1.random"]))
mutable struct SubClass6 <: AbstractSubClass6

end

called = set()
randrange(SubClass6(), 42)
assertEqual(self, called, Set(["Mixin2.getrandbits"]))
mutable struct SubClass7 <: AbstractSubClass7

end

called = set()
randrange(SubClass7(), 42)
assertEqual(self, called, Set(["Mixin1.random"]))
mutable struct SubClass8 <: AbstractSubClass8

end

called = set()
randrange(SubClass8(), 42)
assertEqual(self, called, Set(["Mixin2.getrandbits"]))
end

mutable struct TestModule <: AbstractTestModule

end
function testMagicConstants(self::TestModule)
assertAlmostEqual(self, random.NV_MAGICCONST, 1.71552776992141)
assertAlmostEqual(self, random.TWOPI, 6.28318530718)
assertAlmostEqual(self, random.LOG4, 1.38629436111989)
assertAlmostEqual(self, random.SG_MAGICCONST, 2.50407739677627)
end

function test__all__(self::TestModule)
@test set(random.__all__) <= set(dir(random))
end

function test_after_fork(self::TestModule)
r, w = pipe(os)
pid = fork(os)
if pid == 0
try
val = getrandbits(random, 128)
readline(w) do f 
write(f, string(val))
end
finally
_exit(os, 0)
end
else
close(os, w)
val = getrandbits(random, 128)
readline(r) do f 
child_val = eval(read(f))
end
assertNotEqual(self, val, child_val)
wait_process(support, pid, 0)
end
end

function main()
system_random__test_basic_ops = SystemRandom_TestBasicOps()
test_autoseed(system_random__test_basic_ops)
test_saverestore(system_random__test_basic_ops)
test_seedargs(system_random__test_basic_ops)
test_gauss(system_random__test_basic_ops)
test_pickling(system_random__test_basic_ops)
test_53_bits_per_float(system_random__test_basic_ops)
test_bigrand(system_random__test_basic_ops)
test_bigrand_ranges(system_random__test_basic_ops)
test_rangelimits(system_random__test_basic_ops)
test_randrange_nonunit_step(system_random__test_basic_ops)
test_randrange_errors(system_random__test_basic_ops)
test_randrange_argument_handling(system_random__test_basic_ops)
test_randrange_step(system_random__test_basic_ops)
test_randbelow_logic(system_random__test_basic_ops)
mersenne_twister__test_basic_ops = MersenneTwister_TestBasicOps()
test_guaranteed_stable(mersenne_twister__test_basic_ops)
test_bug_27706(mersenne_twister__test_basic_ops)
test_bug_31478(mersenne_twister__test_basic_ops)
test_bug_31482(mersenne_twister__test_basic_ops)
test_setstate_first_arg(mersenne_twister__test_basic_ops)
test_setstate_middle_arg(mersenne_twister__test_basic_ops)
test_referenceImplementation(mersenne_twister__test_basic_ops)
test_strong_reference_implementation(mersenne_twister__test_basic_ops)
test_long_seed(mersenne_twister__test_basic_ops)
test_53_bits_per_float(mersenne_twister__test_basic_ops)
test_bigrand(mersenne_twister__test_basic_ops)
test_bigrand_ranges(mersenne_twister__test_basic_ops)
test_rangelimits(mersenne_twister__test_basic_ops)
test_getrandbits(mersenne_twister__test_basic_ops)
test_randrange_uses_getrandbits(mersenne_twister__test_basic_ops)
test_randbelow_logic(mersenne_twister__test_basic_ops)
test_randbelow_without_getrandbits(mersenne_twister__test_basic_ops)
test_randrange_bug_1590891(mersenne_twister__test_basic_ops)
test_choices_algorithms(mersenne_twister__test_basic_ops)
test_randbytes(mersenne_twister__test_basic_ops)
test_randbytes_getrandbits(mersenne_twister__test_basic_ops)
test_sample_counts_equivalence(mersenne_twister__test_basic_ops)
test_distributions = TestDistributions()
test_zeroinputs(test_distributions)
test_avg_std(test_distributions)
test_constant(test_distributions)
test_von_mises_range(test_distributions)
test_von_mises_large_kappa(test_distributions)
test_gammavariate_errors(test_distributions)
test_gammavariate_alpha_greater_one(test_distributions)
test_gammavariate_alpha_equal_one(test_distributions)
test_gammavariate_alpha_equal_one_equals_expovariate(test_distributions)
test_gammavariate_alpha_between_zero_and_one(test_distributions)
test_betavariate_return_zero(test_distributions)
test_random_subclassing = TestRandomSubclassing()
test_random_subclass_with_kwargs(test_random_subclassing)
test_subclasses_overriding_methods(test_random_subclassing)
test_module = TestModule()
testMagicConstants(test_module)
test__all__(test_module)
test_after_fork(test_module)
end

main()