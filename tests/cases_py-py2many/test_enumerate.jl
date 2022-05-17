using Test




import gc

abstract type AbstractG end
abstract type AbstractI end
abstract type AbstractIg end
abstract type AbstractX end
abstract type AbstractE end
abstract type AbstractN end
abstract type AbstractPickleTest end
abstract type AbstractEnumerateTestCase end
abstract type AbstractMyEnum <: Abstractenumerate end
abstract type AbstractSubclassTestCase <: AbstractEnumerateTestCase end
abstract type AbstractTestEmpty <: AbstractEnumerateTestCase end
abstract type AbstractTestBig <: AbstractEnumerateTestCase end
abstract type AbstractTestReversed end
abstract type AbstractA end
abstract type AbstractSeqWithWeirdLen end
abstract type AbstractSeq end
abstract type AbstractNoLen <: Abstractobject end
abstract type AbstractNoGetItem <: Abstractobject end
abstract type AbstractBlocked <: Abstractobject end
abstract type AbstractEnumerateStartTestCase <: AbstractEnumerateTestCase end
abstract type AbstractTestStart <: AbstractEnumerateStartTestCase end
abstract type AbstractTestLongStart <: AbstractEnumerateStartTestCase end
mutable struct G <: AbstractG
#= Sequence using __getitem__ =#
seqn
end
function __getitem__(self::G, i)
return self.seqn[i + 1]
end

mutable struct I <: AbstractI
#= Sequence using iterator protocol =#
seqn
i::Int64
end
function __iter__(self::I)
return self
end

function __next__(self::I)
if self.i >= length(self.seqn)
throw(StopIteration)
end
v = self.seqn[self.i + 1]
self.i += 1
return v
end

mutable struct Ig <: AbstractIg
#= Sequence using iterator protocol defined with a generator =#
seqn
i::Int64
end
function __iter__(self::Ig)
Channel() do ch___iter__ 
for val in self.seqn
put!(ch___iter__, val)
end
end
end

mutable struct X <: AbstractX
#= Missing __getitem__ and __iter__ =#
seqn
i::Int64
end
function __next__(self::X)
if self.i >= length(self.seqn)
throw(StopIteration)
end
v = self.seqn[self.i + 1]
self.i += 1
return v
end

mutable struct E <: AbstractE
#= Test propagation of exceptions =#
seqn
i::Int64
end
function __iter__(self::E)
return self
end

function __next__(self::E)
3 ÷ 0
end

mutable struct N <: AbstractN
#= Iterator missing __next__() =#
seqn
i::Int64
end
function __iter__(self::N)
return self
end

mutable struct PickleTest <: AbstractPickleTest

end
function check_pickle(self::PickleTest, itorg, seq)
for proto in 0:pickle.HIGHEST_PROTOCOL
d = dumps(pickle, itorg, proto)
it = loads(pickle, d)
assertEqual(self, type_(itorg), type_(it))
assertEqual(self, collect(it), seq)
it = loads(pickle, d)
try
next(it)
catch exn
if exn isa StopIteration
assertFalse(self, seq[2:end])
continue;
end
end
d = dumps(pickle, it, proto)
it = loads(pickle, d)
assertEqual(self, collect(it), seq[2:end])
end
end

mutable struct EnumerateTestCase <: unittest.TestCase
res
seq
enum

                    EnumerateTestCase(res, seq, enum = enumerate) =
                        new(res, seq, enum)
end
function test_basicfunction(self::EnumerateTestCase)
@test (type_(enum(self, self.seq)) == self.enum)
e = enum(self, self.seq)
@test ((x for x in e) == e)
@test (collect(enum(self, self.seq)) == self.res)
self.enum.__doc__
end

function test_pickle(self::EnumerateTestCase)
check_pickle(self, enum(self, self.seq), self.res)
end

function test_getitemseqn(self::EnumerateTestCase)
@test (collect(enum(self, G(self.seq))) == self.res)
e = enum(self, G(""))
@test_throws StopIteration next(e)
end

function test_iteratorseqn(self::EnumerateTestCase)
@test (collect(enum(self, I(self.seq))) == self.res)
e = enum(self, I(""))
@test_throws StopIteration next(e)
end

function test_iteratorgenerator(self::EnumerateTestCase)
@test (collect(enum(self, Ig(self.seq))) == self.res)
e = enum(self, Ig(""))
@test_throws StopIteration next(e)
end

function test_noniterable(self::EnumerateTestCase)
@test_throws TypeError self.enum(X(self.seq))
end

function test_illformediterable(self::EnumerateTestCase)
@test_throws TypeError self.enum(N(self.seq))
end

function test_exception_propagation(self::EnumerateTestCase)
@test_throws ZeroDivisionError list(enum(self, E(self.seq)))
end

function test_argumentcheck(self::EnumerateTestCase)
@test_throws TypeError self.enum()
@test_throws TypeError self.enum(1)
@test_throws TypeError self.enum("abc", "a")
@test_throws TypeError self.enum("abc", 2, 3)
end

function test_tuple_reuse(self::EnumerateTestCase)
@test (length(set(map(id, collect(enumerate(self.seq))))) == length(self.seq))
@test (length(set(map(id, enumerate(self.seq)))) == min(1, length(self.seq)))
end

function test_enumerate_result_gc(self::EnumerateTestCase)
it = enum(self, [[]])
collect(gc)
@test is_tracked(gc, next(it))
end

mutable struct MyEnum <: AbstractMyEnum

end

mutable struct SubclassTestCase <: AbstractSubclassTestCase
enum::AbstractMyEnum

                    SubclassTestCase(enum::AbstractMyEnum = MyEnum) =
                        new(enum)
end

mutable struct TestEmpty <: AbstractTestEmpty

end

mutable struct TestBig <: AbstractTestBig
res::Vector
seq

                    TestBig(res::Vector = collect(zip(0:19999, seq)), seq = 10:2:19999) =
                        new(res, seq)
end

mutable struct TestReversed <: unittest.TestCase
called::Bool
__reversed__

                    TestReversed(called::Bool, __reversed__ = nothing) =
                        new(called, __reversed__)
end
function test_simple(self::A)
mutable struct A <: AbstractA

end
function __getitem__(self::A, i)::String
if i < 5
return string(i)
end
throw(StopIteration)
end

function __len__(self::A)::Int64
return 5
end

for data in ("abc", 0:4, tuple(enumerate("abc")), A(), 1:5:16, fromkeys(dict, "abcde"))
assertEqual(self, collect(data)[end:-1:begin], collect(reversed(data)))
end
assertRaises(self, TypeError, reversed, [], 1)
end

function test_range_optimization(self::TestReversed)
x = 0:0
@test (type_(reversed(x)) == type_((x for x in x)))
end

function test_len(self::SeqWithWeirdLen)
for s in ("hello", tuple("hello"), collect("hello"), 0:4)
assertEqual(self, length_hint(operator, reversed(s)), length(s))
r = reversed(s)
collect(r)
assertEqual(self, length_hint(operator, r), 0)
end
mutable struct SeqWithWeirdLen <: AbstractSeqWithWeirdLen
called::Bool
end
function __len__(self::SeqWithWeirdLen)::Int64
if !(self.called)
self.called = true
return 10
end
throw(ZeroDivisionError)
end

function __getitem__(self::SeqWithWeirdLen, index)
return index
end

r = reversed(SeqWithWeirdLen())
assertRaises(self, ZeroDivisionError, operator.length_hint, r)
end

function test_gc(self::Seq)
mutable struct Seq <: AbstractSeq

end
function __len__(self::Seq)::Int64
return 10
end

function __getitem__(self::Seq, index)
return index
end

s = Seq()
r = reversed(s)
s.r = r
end

function test_args(self::TestReversed)
@test_throws TypeError reversed()
@test_throws TypeError reversed([], "extra")
end

function test_bug1229429(self::TestReversed)
function f()
#= pass =#
end

r = object()
f.__reversed__ = object()
rc = getrefcount(sys, r)
for i in 0:9
try
reversed(f)
catch exn
if exn isa TypeError
#= pass =#
end
end
end
@test (rc == getrefcount(sys, r))
end

function test_objmethods(self::Blocked)
mutable struct NoLen <: AbstractNoLen

end
function __getitem__(self::NoLen, i)::Int64
return 1
end

nl = NoLen()
assertRaises(self, TypeError, reversed, nl)
mutable struct NoGetItem <: AbstractNoGetItem

end
function __len__(self::NoGetItem)::Int64
return 2
end

ngi = NoGetItem()
assertRaises(self, TypeError, reversed, ngi)
mutable struct Blocked <: AbstractBlocked
__reversed__

                    Blocked(__reversed__ = nothing) =
                        new(__reversed__)
end
function __getitem__(self::Blocked, i)::Int64
return 1
end

function __len__(self::Blocked)::Int64
return 2
end

b = Blocked()
assertRaises(self, TypeError, reversed, b)
end

function test_pickle(self::TestReversed)
for data in ("abc", 0:4, tuple(enumerate("abc")), 1:5:16)
check_pickle(self, reversed(data), collect(data)[end:-1:begin])
end
end

mutable struct EnumerateStartTestCase <: AbstractEnumerateStartTestCase
seq
res
end
function test_basicfunction(self::EnumerateStartTestCase)
e = enum(self, self.seq)
assertEqual(self, (x for x in e), e)
assertEqual(self, collect(enum(self, self.seq)), self.res)
end

mutable struct TestStart <: AbstractTestStart
enum

                    TestStart(enum = (self, i) -> enumerate(i)) =
                        new(enum)
end

mutable struct TestLongStart <: AbstractTestLongStart
enum

                    TestLongStart(enum = (self, i) -> enumerate(i)) =
                        new(enum)
end

function main()
enumerate_test_case = EnumerateTestCase()
test_basicfunction(enumerate_test_case)
test_pickle(enumerate_test_case)
test_getitemseqn(enumerate_test_case)
test_iteratorseqn(enumerate_test_case)
test_iteratorgenerator(enumerate_test_case)
test_noniterable(enumerate_test_case)
test_illformediterable(enumerate_test_case)
test_exception_propagation(enumerate_test_case)
test_argumentcheck(enumerate_test_case)
test_tuple_reuse(enumerate_test_case)
test_enumerate_result_gc(enumerate_test_case)
test_reversed = TestReversed()
test_simple(test_reversed)
test_range_optimization(test_reversed)
test_len(test_reversed)
test_gc(test_reversed)
test_args(test_reversed)
test_bug1229429(test_reversed)
test_objmethods(test_reversed)
test_pickle(test_reversed)
end

main()