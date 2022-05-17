using Test





using test.support.os_helper: TESTFN, unlink



abstract type AbstractBasicIterClass end
abstract type AbstractIteratingSequenceClass end
abstract type AbstractIteratorProxyClass end
abstract type AbstractSequenceClass end
abstract type AbstractSequenceProxyClass end
abstract type AbstractUnlimitedSequenceClass end
abstract type AbstractDefaultIterClass end
abstract type AbstractNoIterClass end
abstract type AbstractBadIterableClass end
abstract type AbstractTestCase end
abstract type AbstractIterClass <: Abstractobject end
abstract type AbstractC <: Abstractobject end
abstract type AbstractMySequenceClass <: AbstractSequenceClass end
abstract type AbstractBoolean end
abstract type AbstractSeq end
abstract type AbstractSeqIter end
abstract type AbstractIntsFrom end
abstract type AbstractNoGuessLen5 end
abstract type AbstractGuess3Len5 <: AbstractNoGuessLen5 end
abstract type AbstractGuess30Len5 <: AbstractNoGuessLen5 end
abstract type AbstractOhPhooey end
abstract type AbstractIterator end
abstract type AbstractWhatever end
abstract type AbstractBadIterator <: Abstractobject end
TRIPLETS = [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 2, 0), (0, 2, 1), (0, 2, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2), (2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 1, 0), (2, 1, 1), (2, 1, 2), (2, 2, 0), (2, 2, 1), (2, 2, 2)]
mutable struct BasicIterClass <: AbstractBasicIterClass
n
i::Int64
end
function __next__(self::BasicIterClass)::Int64
res = self.i
if res >= self.n
throw(StopIteration)
end
self.i = res + 1
return res
end

function __iter__(self::BasicIterClass)
return self
end

mutable struct IteratingSequenceClass <: AbstractIteratingSequenceClass
n
end
function __iter__(self::IteratingSequenceClass)::BasicIterClass
return BasicIterClass(self.n)
end

mutable struct IteratorProxyClass <: AbstractIteratorProxyClass
i
end
function __next__(self::IteratorProxyClass)
return next(self.i)
end

function __iter__(self::IteratorProxyClass)
return self
end

mutable struct SequenceClass <: AbstractSequenceClass
n
end
function __getitem__(self::SequenceClass, i)
if 0 <= i < self.n
return i
else
throw(IndexError)
end
end

mutable struct SequenceProxyClass <: AbstractSequenceProxyClass
s
end
function __getitem__(self::SequenceProxyClass, i)
return self.s[i + 1]
end

mutable struct UnlimitedSequenceClass <: AbstractUnlimitedSequenceClass

end
function __getitem__(self::UnlimitedSequenceClass, i)
return i
end

mutable struct DefaultIterClass <: AbstractDefaultIterClass

end

mutable struct NoIterClass <: AbstractNoIterClass
__iter__

                    NoIterClass(__iter__ = nothing) =
                        new(__iter__)
end
function __getitem__(self::NoIterClass, i)
return i
end

mutable struct BadIterableClass <: AbstractBadIterableClass

end
function __iter__(self::BadIterableClass)
throw(ZeroDivisionError)
end

mutable struct TestCase <: AbstractTestCase
finish
i::Int64
it
start
truth
vals
count::Int64

                    TestCase(finish, i::Int64, it, start, truth, vals, count::Int64 = 0) =
                        new(finish, i, it, start, truth, vals, count)
end
function check_iterator(self::TestCase, it, seq, pickle = true)
if pickle
check_pickle(self, it, seq)
end
res = []
while true
try
val = next(it)
catch exn
if exn isa StopIteration
break;
end
end
push!(res, val)
end
@test (res == seq)
end

function check_for_loop(self::TestCase, expr, seq, pickle = true)
if pickle
check_pickle(self, (x for x in expr), seq)
end
res = []
for val in expr
push!(res, val)
end
@test (res == seq)
end

function check_pickle(self::TestCase, itorg, seq)
for proto in 0:pickle.HIGHEST_PROTOCOL
d = dumps(pickle, itorg, proto)
it = loads(pickle, d)
@test isa(it, collections.abc.Iterator)
@test (collect(it) == seq)
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
@test (collect(it) == seq[2:end])
end
end

function test_iter_basic(self::TestCase)
check_iterator(self, (x for x in 0:9), collect(0:9))
end

function test_iter_idempotency(self::TestCase)
seq = collect(0:9)
it = (x for x in seq)
it2 = (x for x in it)
@test it == it2
end

function test_iter_for_loop(self::TestCase)
check_for_loop(self, (x for x in 0:9), collect(0:9))
end

function test_iter_independence(self::TestCase)
seq = 0:2
res = []
for i in (x for x in seq)
for j in (x for x in seq)
for k in (x for x in seq)
push!(res, (i, j, k))
end
end
end
@test (res == TRIPLETS)
end

function test_nested_comprehensions_iter(self::TestCase)
seq = 0:2
res = [(i, j, k) for i in (x for x in seq) for j in (x for x in seq) for k in (x for x in seq)]
@test (res == TRIPLETS)
end

function test_nested_comprehensions_for(self::TestCase)
seq = 0:2
res = [(i, j, k) for i in seq for j in seq for k in seq]
@test (res == TRIPLETS)
end

function test_iter_class_for(self::TestCase)
check_for_loop(self, IteratingSequenceClass(10), collect(0:9))
end

function test_iter_class_iter(self::TestCase)
check_iterator(self, (x for x in IteratingSequenceClass(10)), collect(0:9))
end

function test_seq_class_for(self::TestCase)
check_for_loop(self, SequenceClass(10), collect(0:9))
end

function test_seq_class_iter(self::TestCase)
check_iterator(self, (x for x in SequenceClass(10)), collect(0:9))
end

function test_mutating_seq_class_iter_pickle(self::TestCase)
orig = SequenceClass(5)
for proto in 0:pickle.HIGHEST_PROTOCOL
itorig = (x for x in orig)
d = dumps(pickle, (itorig, orig), proto)
it, seq = loads(pickle, d)
seq.n = 7
assertIs(self, type_(it), type_(itorig))
@test (collect(it) == collect(0:6))
next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, seq = loads(pickle, d)
seq.n = 7
assertIs(self, type_(it), type_(itorig))
@test (collect(it) == collect(1:6))
for i in 1:4
next(itorig)
end
d = dumps(pickle, (itorig, orig), proto)
it, seq = loads(pickle, d)
seq.n = 7
assertIs(self, type_(it), type_(itorig))
@test (collect(it) == collect(5:6))
@test_throws StopIteration next(itorig)
d = dumps(pickle, (itorig, orig), proto)
it, seq = loads(pickle, d)
seq.n = 7
@test isa(it, collections.abc.Iterator)
@test (collect(it) == [])
end
end

function test_mutating_seq_class_exhausted_iter(self::TestCase)
a = SequenceClass(5)
exhit = (x for x in a)
empit = (x for x in a)
for x in exhit
next(empit)
end
a.n = 7
@test (collect(exhit) == [])
@test (collect(empit) == [5, 6])
@test (collect(a) == [0, 1, 2, 3, 4, 5, 6])
end

function test_new_style_iter_class(self::IterClass)
mutable struct IterClass <: AbstractIterClass

end
function __iter__(self::IterClass)
return self
end

assertRaises(self, TypeError, iter, IterClass())
end

function test_iter_callable(self::C)
mutable struct C <: AbstractC
i::Int64
end
function __call__(self::C)::Int64
i = self.i
self.i = i + 1
if i > 100
throw(IndexError)
end
return i
end

check_iterator(self, (x for x in C()), collect(0:9))
end

function test_iter_function(self::TestCase)
function spam(state = [0])
i = state[1]
state[1] = i + 1
return i
end

check_iterator(self, (x for x in spam), collect(0:9))
end

function test_iter_function_stop(self::TestCase)
function spam(state = [0])
i = state[1]
if i == 10
throw(StopIteration)
end
state[1] = i + 1
return i
end

check_iterator(self, (x for x in spam), collect(0:9))
end

function test_exception_function(self::TestCase)
function spam(state = [0])
i = state[1]
state[1] = i + 1
if i == 10
throw(RuntimeError)
end
return i
end

res = []
try
for x in (x for x in spam)
push!(res, x)
end
catch exn
if exn isa RuntimeError
@test (res == collect(0:9))
end
end
end

function test_exception_sequence(self::MySequenceClass)
mutable struct MySequenceClass <: AbstractMySequenceClass

end
function __getitem__(self::MySequenceClass, i)
if i == 10
throw(RuntimeError)
end
return __getitem__(SequenceClass, self)
end

res = []
try
for x in MySequenceClass(20)
push!(res, x)
end
catch exn
if exn isa RuntimeError
assertEqual(self, res, collect(0:9))
end
end
end

function test_stop_sequence(self::MySequenceClass)
mutable struct MySequenceClass <: AbstractMySequenceClass

end
function __getitem__(self::MySequenceClass, i)
if i == 10
throw(StopIteration)
end
return __getitem__(SequenceClass, self)
end

check_for_loop(self, MySequenceClass(20), collect(0:9))
end

function test_iter_big_range(self::TestCase)
check_for_loop(self, (x for x in 0:9999), collect(0:9999))
end

function test_iter_empty(self::TestCase)
check_for_loop(self, (x for x in []), [])
end

function test_iter_tuple(self::TestCase)
check_for_loop(self, (x for x in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)), collect(0:9))
end

function test_iter_range(self::TestCase)
check_for_loop(self, (x for x in 0:9), collect(0:9))
end

function test_iter_string(self::TestCase)
check_for_loop(self, (x for x in "abcde"), ["a", "b", "c", "d", "e"])
end

function test_iter_dict(self::TestCase)
dict = Dict()
for i in 0:9
dict[i] = nothing
end
check_for_loop(self, dict, collect(keys(dict)))
end

function test_iter_file(self::TestCase)
f = readline(TESTFN)
try
for i in 0:4
write(f, "%d\n" % i)
end
finally
close(f)
end
f = readline(TESTFN)
try
check_for_loop(self, f, ["0\n", "1\n", "2\n", "3\n", "4\n"])
check_for_loop(self, f, [])
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_builtin_list(self::TestCase)
@test (collect(SequenceClass(5)) == collect(0:4))
@test (collect(SequenceClass(0)) == [])
@test (collect(()) == [])
d = Dict("one" => 1, "two" => 2, "three" => 3)
@test (collect(d) == collect(keys(d)))
@test_throws TypeError list(list)
@test_throws TypeError list(42)
f = readline(TESTFN)
try
for i in 0:4
write(f, "%d\n" % i)
end
finally
close(f)
end
f = readline(TESTFN)
try
@test (collect(f) == ["0\n", "1\n", "2\n", "3\n", "4\n"])
seek(f, 0, 0)
@test (collect(f) == ["0\n", "1\n", "2\n", "3\n", "4\n"])
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_builtin_tuple(self::TestCase)
@test (tuple(SequenceClass(5)) == (0, 1, 2, 3, 4))
@test (tuple(SequenceClass(0)) == ())
@test (tuple([]) == ())
@test (tuple(()) == ())
@test (tuple("abc") == ("a", "b", "c"))
d = Dict("one" => 1, "two" => 2, "three" => 3)
@test (tuple(d) == tuple(keys(d)))
@test_throws TypeError tuple(list)
@test_throws TypeError tuple(42)
f = readline(TESTFN)
try
for i in 0:4
write(f, "%d\n" % i)
end
finally
close(f)
end
f = readline(TESTFN)
try
@test (tuple(f) == ("0\n", "1\n", "2\n", "3\n", "4\n"))
seek(f, 0, 0)
@test (tuple(f) == ("0\n", "1\n", "2\n", "3\n", "4\n"))
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_builtin_filter(self::Seq)
assertEqual(self, collect(filter(nothing, SequenceClass(5))), collect(1:4))
assertEqual(self, collect(filter(nothing, SequenceClass(0))), [])
assertEqual(self, collect(filter(nothing, ())), [])
assertEqual(self, collect(filter(nothing, "abc")), ["a", "b", "c"])
d = Dict("one" => 1, "two" => 2, "three" => 3)
assertEqual(self, collect(filter(nothing, d)), collect(keys(d)))
assertRaises(self, TypeError, filter, nothing, list)
assertRaises(self, TypeError, filter, nothing, 42)
mutable struct Boolean <: AbstractBoolean
truth
end
function __bool__(self::Boolean)
return self.truth
end

bTrue = Boolean(true)
bFalse = Boolean(false)
mutable struct Seq <: AbstractSeq
i::Int64
vals
end
function __iter__(self::SeqIter)::SeqIter
mutable struct SeqIter <: AbstractSeqIter
i::Int64
vals
end
function __iter__(self::SeqIter)
return self
end

function __next__(self::SeqIter)
i = self.i
self.i = i + 1
if i < length(self.vals)
return self.vals[i + 1]
else
throw(StopIteration)
end
end

return SeqIter(self.vals)
end

seq = Seq(repeat([bTrue, bFalse],25)...)
assertEqual(self, collect(filter((x) -> !(x), seq)), repeat([bFalse],25))
assertEqual(self, collect(filter((x) -> !(x), (x for x in seq))), repeat([bFalse],25))
end

function test_builtin_max_min(self::TestCase)
@test (max(SequenceClass(5)) == 4)
@test (min(SequenceClass(5)) == 0)
@test (max(8, -1) == 8)
@test (min(8, -1) == -1)
d = Dict("one" => 1, "two" => 2, "three" => 3)
@test (max(d) == "two")
@test (min(d) == "one")
@test (max(values(d)) == 3)
@test (min((x for x in values(d))) == 1)
f = readline(TESTFN)
try
write(f, "medium line\n")
write(f, "xtra large line\n")
write(f, "itty-bitty line\n")
finally
close(f)
end
f = readline(TESTFN)
try
@test (min(f) == "itty-bitty line\n")
seek(f, 0, 0)
@test (max(f) == "xtra large line\n")
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_builtin_map(self::TestCase)
@test (collect(map((x) -> x + 1, SequenceClass(5))) == collect(1:5))
d = Dict("one" => 1, "two" => 2, "three" => 3)
@test (collect(map((k, d) -> (k, d[k]), d)) == collect(items(d)))
dkeys = collect(keys(d))
expected = [(i < length(d) && dkeys[i + 1] || nothing, i, i < length(d) && dkeys[i + 1] || nothing) for i in 0:2]
f = readline(TESTFN)
try
for i in 0:9
write(f, "xy"*i * "\n")
end
finally
close(f)
end
f = readline(TESTFN)
try
@test (collect(map(len, f)) == collect(1:2:20))
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_builtin_zip(self::Guess30Len5)
assertEqual(self, collect(zip()), [])
assertEqual(self, collect(zip([]...)), [])
assertEqual(self, collect(zip([(1, 2), "ab"]...)), [(1, "a"), (2, "b")])
assertRaises(self, TypeError, zip, nothing)
assertRaises(self, TypeError, zip, 0:9, 42)
assertRaises(self, TypeError, zip, 0:9, zip)
assertEqual(self, collect(zip(IteratingSequenceClass(3))), [(0,), (1,), (2,)])
assertEqual(self, collect(zip(SequenceClass(3))), [(0,), (1,), (2,)])
d = Dict("one" => 1, "two" => 2, "three" => 3)
assertEqual(self, collect(items(d)), collect(zip(d, values(d))))
mutable struct IntsFrom <: AbstractIntsFrom
i
end
function __iter__(self::IntsFrom)
return self
end

function __next__(self::IntsFrom)
i = self.i
self.i = i + 1
return i
end

f = readline(TESTFN)
try
write(f, "a\nbbb\ncc\n")
finally
close(f)
end
f = readline(TESTFN)
try
assertEqual(self, collect(zip(IntsFrom(0), f)), [(0, "a\n", -100), (1, "bbb\n", -99), (2, "cc\n", -98)])
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
assertEqual(self, collect(zip(0:4)), [(i,) for i in 0:4])
mutable struct NoGuessLen5 <: AbstractNoGuessLen5

end
function __getitem__(self::NoGuessLen5, i)
if i >= 5
throw(IndexError)
end
return i
end

mutable struct Guess3Len5 <: AbstractGuess3Len5

end
function __len__(self::Guess3Len5)::Int64
return 3
end

mutable struct Guess30Len5 <: AbstractGuess30Len5

end
function __len__(self::Guess30Len5)::Int64
return 30
end

function lzip()::Vector
return collect(zip(args...))
end

assertEqual(self, length(Guess3Len5()), 3)
assertEqual(self, length(Guess30Len5()), 30)
assertEqual(self, lzip(), lzip())
assertEqual(self, lzip(), lzip())
assertEqual(self, lzip(), lzip())
expected = [(i, i) for i in 0:4]
for x in (NoGuessLen5(), Guess3Len5(), Guess30Len5())
for y in (NoGuessLen5(), Guess3Len5(), Guess30Len5())
assertEqual(self, lzip(), expected)
end
end
end

function test_unicode_join_endcase(self::OhPhooey)
mutable struct OhPhooey <: AbstractOhPhooey
i::Int64
it
end
function __iter__(self::OhPhooey)
return self
end

function __next__(self::OhPhooey)::String
i = self.i
self.i = i + 1
if i == 2
return "fooled you!"
end
return next(self.it)
end

f = readline(TESTFN)
try
write(f, "a\n" * "b\n" * "c\n")
finally
close(f)
end
f = readline(TESTFN)
try
got = join(OhPhooey(f), " - ")
assertEqual(self, got, "a\n - b\n - fooled you! - c\n")
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_in_and_not_in(self::TestCase)
for sc5 in (IteratingSequenceClass(5), SequenceClass(5))
for i in 0:4
assertIn(self, i, sc5)
end
for i in ("abc", -1, 5, 42.42, (3, 4), [], Dict(1 => 1), 3 - 12im, sc5)
assertNotIn(self, i, sc5)
end
end
assertIn(self, ALWAYS_EQ, IteratorProxyClass((x for x in [1])))
assertIn(self, ALWAYS_EQ, SequenceProxyClass([1]))
assertNotIn(self, ALWAYS_EQ, IteratorProxyClass((x for x in [NEVER_EQ])))
assertNotIn(self, ALWAYS_EQ, SequenceProxyClass([NEVER_EQ]))
assertIn(self, NEVER_EQ, IteratorProxyClass((x for x in [ALWAYS_EQ])))
assertIn(self, NEVER_EQ, SequenceProxyClass([ALWAYS_EQ]))
@test_throws TypeError () -> 3 ∈ 12()
@test_throws TypeError () -> 3 ∉ map()
@test_throws ZeroDivisionError () -> 3 ∈ BadIterableClass()()
d = Dict("one" => 1, "two" => 2, "three" => 3, 1im => 2im)
for k in d
assertIn(self, k, d)
assertNotIn(self, k, values(d))
end
for v in values(d)
assertIn(self, v, values(d))
assertNotIn(self, v, d)
end
for (k, v) in items(d)
assertIn(self, (k, v), items(d))
assertNotIn(self, (v, k), items(d))
end
f = readline(TESTFN)
try
write(f, "a\nb\nc\n")
finally
close(f)
end
f = readline(TESTFN)
try
for chunk in "abc"
seek(f, 0, 0)
assertNotIn(self, chunk, f)
seek(f, 0, 0)
assertIn(self, chunk + "\n", f)
end
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_countOf(self::TestCase)
@test (countOf([1, 2, 2, 3, 2, 5], 2) == 3)
@test (countOf((1, 2, 2, 3, 2, 5), 2) == 3)
@test (countOf("122325", "2") == 3)
@test (countOf("122325", "6") == 0)
@test_throws TypeError countOf(42, 1)
@test_throws TypeError countOf(countOf, countOf)
d = Dict("one" => 3, "two" => 3, "three" => 3, 1im => 2im)
for k in d
@test (countOf(d, k) == 1)
end
@test (countOf(values(d), 3) == 3)
@test (countOf(values(d), 2im) == 1)
@test (countOf(values(d), 1im) == 0)
f = readline(TESTFN)
try
write(f, "a\nb\nc\nb\n")
finally
close(f)
end
f = readline(TESTFN)
try
for (letter, count) in (("a", 1), ("b", 2), ("c", 1), ("d", 0))
seek(f, 0, 0)
@test (countOf(f, letter + "\n") == count)
end
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_indexOf(self::TestCase)
@test (indexOf([1, 2, 2, 3, 2, 5], 1) == 0)
@test (indexOf((1, 2, 2, 3, 2, 5), 2) == 1)
@test (indexOf((1, 2, 2, 3, 2, 5), 3) == 3)
@test (indexOf((1, 2, 2, 3, 2, 5), 5) == 5)
@test_throws ValueError indexOf((1, 2, 2, 3, 2, 5), 0)
@test_throws ValueError indexOf((1, 2, 2, 3, 2, 5), 6)
@test (indexOf("122325", "2") == 1)
@test (indexOf("122325", "5") == 5)
@test_throws ValueError indexOf("122325", "6")
@test_throws TypeError indexOf(42, 1)
@test_throws TypeError indexOf(indexOf, indexOf)
@test_throws ZeroDivisionError indexOf(BadIterableClass(), 1)
f = readline(TESTFN)
try
write(f, "a\nb\nc\nd\ne\n")
finally
close(f)
end
f = readline(TESTFN)
try
fiter = (x for x in f)
@test (indexOf(fiter, "b\n") == 1)
@test (indexOf(fiter, "d\n") == 1)
@test (indexOf(fiter, "e\n") == 0)
@test_throws ValueError indexOf(fiter, "a\n")
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
iclass = IteratingSequenceClass(3)
for i in 0:2
@test (indexOf(iclass, i) == i)
end
@test_throws ValueError indexOf(iclass, -1)
end

function test_writelines(self::Whatever)
f = readline(TESTFN)
try
assertRaises(self, TypeError, f.writelines, nothing)
assertRaises(self, TypeError, f.writelines, 42)
writelines(f, ["1\n", "2\n"])
writelines(f, ("3\n", "4\n"))
writelines(f, Dict("5\n" => nothing))
writelines(f, Dict())
mutable struct Iterator <: AbstractIterator
start
finish
i
end
function __next__(self::Iterator)::String
if self.i >= self.finish
throw(StopIteration)
end
result = string(self.i) * "\n"
self.i += 1
return result
end

function __iter__(self::Iterator)
return self
end

mutable struct Whatever <: AbstractWhatever
start
finish
end
function __iter__(self::Whatever)::Iterator
return Iterator(self.start, self.finish)
end

writelines(f, Whatever(6, 6 + 2000))
close(f)
f = readline(TESTFN)
expected = [string(i) * "\n" for i in 1:2005]
assertEqual(self, collect(f), expected)
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
end

function test_unpack_iter(self::TestCase)
a, b = (1, 2)
@test ((a, b) == (1, 2))
a, b, c = IteratingSequenceClass(3)
@test ((a, b, c) == (0, 1, 2))
try
a, b = IteratingSequenceClass(3)
catch exn
if exn isa ValueError
#= pass =#
end
end
try
a, b, c = IteratingSequenceClass(2)
catch exn
if exn isa ValueError
#= pass =#
end
end
try
a, b, c = len
catch exn
if exn isa TypeError
#= pass =#
end
end
a, b, c = values(Dict(1 => 42, 2 => 42, 3 => 42))
@test ((a, b, c) == (42, 42, 42))
f = readline(TESTFN)
lines = ("a\n", "bb\n", "ccc\n")
try
for line in lines
write(f, line)
end
finally
close(f)
end
f = readline(TESTFN)
try
a, b, c = f
@test ((a, b, c) == lines)
finally
close(f)
try
unlink(TESTFN)
catch exn
if exn isa OSError
#= pass =#
end
end
end
(a, b), (c,) = (IteratingSequenceClass(2), Dict(42 => 24))
@test ((a, b, c) == (0, 1, 42))
end

function test_ref_counting_behavior(self::C)
mutable struct C <: AbstractC
count::Int64

                    C(count::Int64 = 0) =
                        new(count)
end
function __new__(cls)
cls.count += 1
return __new__(object)
end

function __del__(self::C)
cls = self.__class__
@assert(cls.count > 0)
cls.count -= 1
end

x = C()
assertEqual(self, C.count, 1)
#Delete Unsupported
del(x)
assertEqual(self, C.count, 0)
l = [C(), C(), C()]
assertEqual(self, C.count, 3)
try
a, b = (x for x in l)
catch exn
if exn isa ValueError
#= pass =#
end
end
#Delete Unsupported
del(l)
assertEqual(self, C.count, 0)
end

function test_sinkstate_list(self::TestCase)
a = collect(0:4)
b = (x for x in a)
@test (collect(b) == collect(0:4))
append!(a, 5:9)
@test (collect(b) == [])
end

function test_sinkstate_tuple(self::TestCase)
a = (0, 1, 2, 3, 4)
b = (x for x in a)
@test (collect(b) == collect(0:4))
@test (collect(b) == [])
end

function test_sinkstate_string(self::TestCase)
a = "abcde"
b = (x for x in a)
@test (collect(b) == ["a", "b", "c", "d", "e"])
@test (collect(b) == [])
end

function test_sinkstate_sequence(self::TestCase)
a = SequenceClass(5)
b = (x for x in a)
@test (collect(b) == collect(0:4))
a.n = 10
@test (collect(b) == [])
end

function test_sinkstate_callable(self::TestCase)
function spam(state = [0])
i = state[1]
state[1] = i + 1
if i == 10
throw(AssertionError("shouldn\'t have gotten this far"))
end
return i
end

b = (x for x in spam)
@test (collect(b) == collect(0:4))
@test (collect(b) == [])
end

function test_sinkstate_dict(self::TestCase)
a = Dict(1 => 1, 2 => 2, 0 => 0, 4 => 4, 3 => 3)
for b in ((x for x in a), keys(a), items(a), values(a))
b = (x for x in a)
@test (length(collect(b)) == 5)
@test (collect(b) == [])
end
end

function test_sinkstate_yield(self::TestCase)
function gen()
Channel() do ch_gen 
for i in 0:4
put!(ch_gen, i)
end
end
end

b = gen()
@test (collect(b) == collect(0:4))
@test (collect(b) == [])
end

function test_sinkstate_range(self::TestCase)
a = 0:4
b = (x for x in a)
@test (collect(b) == collect(0:4))
@test (collect(b) == [])
end

function test_sinkstate_enumerate(self::TestCase)
a = 0:4
e = enumerate(a)
b = (x for x in e)
@test (collect(b) == collect(zip(0:4, 0:4)))
@test (collect(b) == [])
end

function test_3720(self::BadIterator)
mutable struct BadIterator <: AbstractBadIterator

end
function __iter__(self::BadIterator)
return self
end

function __next__(self::BadIterator)::Int64
#Delete Unsupported
del(next(BadIterator))
return 1
end

try
for i in BadIterator()
#= pass =#
end
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function test_extending_list_with_iterator_does_not_segfault(self::TestCase)
function gen()
Channel() do ch_gen 
for i in 0:499
put!(ch_gen, i)
end
end
end

lst = repeat([0],500)
for i in 0:239
pop(lst, 0)
end
append!(lst, gen())
@test (length(lst) == 760)
end

function test_iter_overflow(self::TestCase)
it = (x for x in UnlimitedSequenceClass())
__setstate__(it, sys.maxsize - 2)
@test (next(it) == sys.maxsize - 2)
@test (next(it) == sys.maxsize - 1)
assertRaises(self, OverflowError) do 
next(it)
end
assertRaises(self, OverflowError) do 
next(it)
end
end

function test_iter_neg_setstate(self::TestCase)
it = (x for x in UnlimitedSequenceClass())
__setstate__(it, -42)
@test (next(it) == 0)
@test (next(it) == 1)
end

function test_free_after_iterating(self::TestCase)
check_free_after_iterating(self, iter, SequenceClass, (0,))
end

function test_error_iter(self::TestCase)
for typ in (DefaultIterClass, NoIterClass)
@test_throws TypeError iter(typ())
end
@test_throws ZeroDivisionError iter(BadIterableClass())
end

function main()
test_case = TestCase()
check_iterator(test_case)
check_for_loop(test_case)
check_pickle(test_case)
test_iter_basic(test_case)
test_iter_idempotency(test_case)
test_iter_for_loop(test_case)
test_iter_independence(test_case)
test_nested_comprehensions_iter(test_case)
test_nested_comprehensions_for(test_case)
test_iter_class_for(test_case)
test_iter_class_iter(test_case)
test_seq_class_for(test_case)
test_seq_class_iter(test_case)
test_mutating_seq_class_iter_pickle(test_case)
test_mutating_seq_class_exhausted_iter(test_case)
test_new_style_iter_class(test_case)
test_iter_callable(test_case)
test_iter_function(test_case)
test_iter_function_stop(test_case)
test_exception_function(test_case)
test_exception_sequence(test_case)
test_stop_sequence(test_case)
test_iter_big_range(test_case)
test_iter_empty(test_case)
test_iter_tuple(test_case)
test_iter_range(test_case)
test_iter_string(test_case)
test_iter_dict(test_case)
test_iter_file(test_case)
test_builtin_list(test_case)
test_builtin_tuple(test_case)
test_builtin_filter(test_case)
test_builtin_max_min(test_case)
test_builtin_map(test_case)
test_builtin_zip(test_case)
test_unicode_join_endcase(test_case)
test_in_and_not_in(test_case)
test_countOf(test_case)
test_indexOf(test_case)
test_writelines(test_case)
test_unpack_iter(test_case)
test_ref_counting_behavior(test_case)
test_sinkstate_list(test_case)
test_sinkstate_tuple(test_case)
test_sinkstate_string(test_case)
test_sinkstate_sequence(test_case)
test_sinkstate_callable(test_case)
test_sinkstate_dict(test_case)
test_sinkstate_yield(test_case)
test_sinkstate_range(test_case)
test_sinkstate_enumerate(test_case)
test_3720(test_case)
test_extending_list_with_iterator_does_not_segfault(test_case)
test_iter_overflow(test_case)
test_iter_neg_setstate(test_case)
test_free_after_iterating(test_case)
test_error_iter(test_case)
end

main()