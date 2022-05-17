using Test
import concurrent.futures
import contextvars
import functools
import gc
import random



try
using _testcapi: hamt
catch exn
if exn isa ImportError
hamt = nothing
end
end
abstract type AbstractContextTest end
abstract type AbstractMyContextVar <: Abstractcontextvars.ContextVar end
abstract type AbstractMyContext <: Abstractcontextvars.Context end
abstract type AbstractMyToken <: Abstractcontextvars.Token end
abstract type AbstractHashKey end
abstract type AbstractKeyStr <: Abstractstr end
abstract type AbstractHaskKeyCrasher end
abstract type AbstractHashingError <: AbstractException end
abstract type AbstractEqError <: AbstractException end
abstract type AbstractHamtTest end
function isolated_context(func)
#= Needed to make reftracking test mode work. =#
function wrapper()
ctx = Context(contextvars)
return run(ctx, func, args..., kwargs)
end

return wrapper
end

mutable struct ContextTest <: AbstractContextTest

end
function test_context_var_new_1(self::ContextTest)
assertRaisesRegex(self, TypeError, "takes exactly 1") do 
ContextVar(contextvars)
end
assertRaisesRegex(self, TypeError, "must be a str") do 
ContextVar(contextvars, 1)
end
c = ContextVar(contextvars, "aaa")
@test (c.name == "aaa")
assertRaises(self, AttributeError) do 
c.name = "bbb"
end
assertNotEqual(self, hash(c), hash("aaa"))
end

function test_context_var_repr_1(self::ContextTest)
c = ContextVar(contextvars, "a")
assertIn(self, "a", repr(c))
c = ContextVar(contextvars, "a", 123)
assertIn(self, "123", repr(c))
lst = []
c = ContextVar(contextvars, "a", lst)
push!(lst, c)
assertIn(self, "...", repr(c))
assertIn(self, "...", repr(lst))
t = set(c, 1)
assertIn(self, repr(c), repr(t))
assertNotIn(self, " used ", repr(t))
reset(c, t)
assertIn(self, " used ", repr(t))
end

function test_context_subclassing_1(self::MyToken)
assertRaisesRegex(self, TypeError, "not an acceptable base type") do 
mutable struct MyContextVar <: AbstractMyContextVar

end

end
assertRaisesRegex(self, TypeError, "not an acceptable base type") do 
mutable struct MyContext <: AbstractMyContext

end

end
assertRaisesRegex(self, TypeError, "not an acceptable base type") do 
mutable struct MyToken <: AbstractMyToken

end

end
end

function test_context_new_1(self::ContextTest)
assertRaisesRegex(self, TypeError, "any arguments") do 
Context(contextvars, 1)
end
assertRaisesRegex(self, TypeError, "any arguments") do 
Context(contextvars, 1, 1)
end
assertRaisesRegex(self, TypeError, "any arguments") do 
Context(contextvars, 1)
end
Context(contextvars, Dict())
end

function test_context_typerrors_1(self::ContextTest)
ctx = Context(contextvars)
assertRaisesRegex(self, TypeError, "ContextVar key was expected") do 
ctx[2]
end
assertRaisesRegex(self, TypeError, "ContextVar key was expected") do 
1 ∈ ctx
end
assertRaisesRegex(self, TypeError, "ContextVar key was expected") do 
get(ctx, 1)
end
end

function test_context_get_context_1(self::ContextTest)
ctx = copy_context(contextvars)
@test isa(self, ctx)
end

function test_context_run_1(self::ContextTest)
ctx = Context(contextvars)
assertRaisesRegex(self, TypeError, "missing 1 required") do 
run(ctx)
end
end

function test_context_run_2(self::ContextTest)
ctx = Context(contextvars)
function func()::Tuple
kwargs["spam"] = "foo"
args += ("bar",)
return (args, kwargs)
end

for f in (func, partial(functools, func))
@test (run(ctx, f) == (("bar",), Dict("spam" => "foo")))
@test (run(ctx, f, 1) == ((1, "bar"), Dict("spam" => "foo")))
@test (run(ctx, f, 2) == (("bar",), Dict("a" => 2, "spam" => "foo")))
@test (run(ctx, f, 11, 2) == ((11, "bar"), Dict("a" => 2, "spam" => "foo")))
a = Dict()
@test (run(ctx, f, 11, a) == ((11, "bar"), Dict("spam" => "foo")))
@test (a == Dict())
end
end

function test_context_run_3(self::ContextTest)
ctx = Context(contextvars)
function func()
1 / 0
end

assertRaises(self, ZeroDivisionError) do 
run(ctx, func)
end
assertRaises(self, ZeroDivisionError) do 
run(ctx, func, 1, 2)
end
assertRaises(self, ZeroDivisionError) do 
run(ctx, func, 1, 2, 123)
end
end

function test_context_run_4(self::ContextTest)
ctx1 = Context(contextvars)
ctx2 = Context(contextvars)
var = ContextVar(contextvars, "var")
function func2()
assertIsNone(self, get(var, nothing))
end

function func1()
assertIsNone(self, get(var, nothing))
set(var, "spam")
run(ctx2, func2)
@test (get(var, nothing) == "spam")
cur = copy_context(contextvars)
@test (length(cur) == 1)
@test (cur[var + 1] == "spam")
return cur
end

returned_ctx = run(ctx1, func1)
@test (ctx1 == returned_ctx)
@test (returned_ctx[var + 1] == "spam")
assertIn(self, var, returned_ctx)
end

function test_context_run_5(self::ContextTest)
ctx = Context(contextvars)
var = ContextVar(contextvars, "var")
function func()
assertIsNone(self, get(var, nothing))
set(var, "spam")
1 / 0
end

assertRaises(self, ZeroDivisionError) do 
run(ctx, func)
end
assertIsNone(self, get(var, nothing))
end

function test_context_run_6(self::ContextTest)
ctx = Context(contextvars)
c = ContextVar(contextvars, "a", 0)
function fun()
@test (get(c) == 0)
assertIsNone(self, get(ctx, c))
set(c, 42)
@test (get(c) == 42)
@test (get(ctx, c) == 42)
end

run(ctx, fun)
end

function test_context_run_7(self::ContextTest)
ctx = Context(contextvars)
function fun()
assertRaisesRegex(self, RuntimeError, "is already entered") do 
run(ctx, fun)
end
end

run(ctx, fun)
end

function test_context_getset_1(self::ContextTest)
c = ContextVar(contextvars, "c")
assertRaises(self, LookupError) do 
get(c)
end
assertIsNone(self, get(c, nothing))
t0 = set(c, 42)
@test (get(c) == 42)
@test (get(c, nothing) == 42)
assertIs(self, t0.old_value, t0.MISSING)
assertIs(self, t0.old_value, contextvars.Token.MISSING)
assertIs(self, t0.var, c)
t = set(c, "spam")
@test (get(c) == "spam")
@test (get(c, nothing) == "spam")
@test (t.old_value == 42)
reset(c, t)
@test (get(c) == 42)
@test (get(c, nothing) == 42)
set(c, "spam2")
assertRaisesRegex(self, RuntimeError, "has already been used") do 
reset(c, t)
end
@test (get(c) == "spam2")
ctx1 = copy_context(contextvars)
assertIn(self, c, ctx1)
reset(c, t0)
assertRaisesRegex(self, RuntimeError, "has already been used") do 
reset(c, t0)
end
assertIsNone(self, get(c, nothing))
assertIn(self, c, ctx1)
@test (ctx1[c + 1] == "spam2")
@test (get(ctx1, c, "aa") == "spam2")
@test (length(ctx1) == 1)
@test (collect(items(ctx1)) == [(c, "spam2")])
@test (collect(values(ctx1)) == ["spam2"])
@test (collect(keys(ctx1)) == [c])
@test (collect(ctx1) == [c])
ctx2 = copy_context(contextvars)
assertNotIn(self, c, ctx2)
assertRaises(self, KeyError) do 
ctx2[c + 1]
end
@test (get(ctx2, c, "aa") == "aa")
@test (length(ctx2) == 0)
@test (collect(ctx2) == [])
end

function test_context_getset_2(self::ContextTest)
v1 = ContextVar(contextvars, "v1")
v2 = ContextVar(contextvars, "v2")
t1 = set(v1, 42)
assertRaisesRegex(self, ValueError, "by a different") do 
reset(v2, t1)
end
end

function test_context_getset_3(self::ContextTest)
c = ContextVar(contextvars, "c", 42)
ctx = Context(contextvars)
function fun()
@test (get(c) == 42)
assertRaises(self, KeyError) do 
ctx[c + 1]
end
assertIsNone(self, get(ctx, c))
@test (get(ctx, c, "spam") == "spam")
assertNotIn(self, c, ctx)
@test (collect(keys(ctx)) == [])
t = set(c, 1)
@test (collect(keys(ctx)) == [c])
@test (ctx[c + 1] == 1)
reset(c, t)
@test (collect(keys(ctx)) == [])
assertRaises(self, KeyError) do 
ctx[c + 1]
end
end

run(ctx, fun)
end

function test_context_getset_4(self::ContextTest)
c = ContextVar(contextvars, "c", 42)
ctx = Context(contextvars)
tok = run(ctx, c.set, 1)
assertRaisesRegex(self, ValueError, "different Context") do 
reset(c, tok)
end
end

function test_context_getset_5(self::ContextTest)
c = ContextVar(contextvars, "c", 42)
set(c, [])
function fun()
set(c, [])
append(get(c), 42)
@test (get(c) == [42])
end

run(copy_context(contextvars), fun)
@test (get(c) == [])
end

function test_context_copy_1(self::ContextTest)
ctx1 = Context(contextvars)
c = ContextVar(contextvars, "c", 42)
function ctx1_fun()
set(c, 10)
ctx2 = copy(ctx1)
@test (ctx2[c + 1] == 10)
set(c, 20)
@test (ctx1[c + 1] == 20)
@test (ctx2[c + 1] == 10)
run(ctx2, ctx2_fun)
@test (ctx1[c + 1] == 20)
@test (ctx2[c + 1] == 30)
end

function ctx2_fun()
@test (get(c) == 10)
set(c, 30)
@test (get(c) == 30)
end

run(ctx1, ctx1_fun)
end

function test_context_threads_1(self::ContextTest)
cvar = ContextVar(contextvars, "cvar")
function sub(num)
for i in 0:9
set(cvar, num + i)
sleep(time, uniform(random, 0.001, 0.05))
@test (get(cvar) == num + i)
end
return num
end

tp = ThreadPoolExecutor(concurrent.futures, 10)
try
results = collect(map(tp, sub, 0:9))
finally
shutdown(tp)
end
@test (results == collect(0:9))
end

mutable struct HashKey <: AbstractHashKey
error_on_eq_to
hash
name
_crasher

            HashKey(hash, name, _crasher = nothing) = begin
                @assert(hash != -1)
                new(hash, name, _crasher )
            end
end
function __repr__(self::HashKey)
return "<Key name:$(self.name) hash:$(self.hash)>"
end

function __hash__(self::HashKey)
if self._crasher != nothing && self._crasher.error_on_hash
throw(HashingError)
end
return self.hash
end

function __eq__(self::HashKey, other)::Bool
if !isa(other, HashKey)
return NotImplemented
end
if self._crasher != nothing && self._crasher.error_on_eq
throw(EqError)
end
if self.error_on_eq_to != nothing && self.error_on_eq_to == other
throw(ValueError("cannot compare $('self') to $('other')"))
end
if other.error_on_eq_to != nothing && other.error_on_eq_to == self
throw(ValueError("cannot compare $('other') to $('self')"))
end
return (self.name, self.hash) == (other.name, other.hash)
end

mutable struct KeyStr <: AbstractKeyStr

end
function __hash__(self::KeyStr)
if HashKey._crasher != nothing && HashKey._crasher.error_on_hash
throw(HashingError)
end
return __hash__(super())
end

function __eq__(self::KeyStr, other)
if HashKey._crasher != nothing && HashKey._crasher.error_on_eq
throw(EqError)
end
return __eq__(super(), other)
end

mutable struct HaskKeyCrasher <: AbstractHaskKeyCrasher
error_on_hash
error_on_eq
end
function __enter__(self::HaskKeyCrasher)
if HashKey._crasher != nothing
throw(RuntimeError("cannot nest crashers"))
end
HashKey._crasher = self
end

function __exit__(self::HaskKeyCrasher)
HashKey._crasher = nothing
end

mutable struct HashingError <: AbstractHashingError

end

mutable struct EqError <: AbstractEqError

end

mutable struct HamtTest <: AbstractHamtTest

end
function test_hashkey_helper_1(self::HamtTest)
k1 = HashKey(10, "aaa")
k2 = HashKey(10, "bbb")
assertNotEqual(self, k1, k2)
@test (hash(k1) == hash(k2))
d = dict()
d[__add__(k1, 1)] = "a"
d[__add__(k2, 1)] = "b"
@test (d[__add__(k1, 1)] == "a")
@test (d[__add__(k2, 1)] == "b")
end

function test_hamt_basics_1(self::HamtTest)
h = hamt()
h = nothing
end

function test_hamt_basics_2(self::HamtTest)
h = hamt()
@test (length(h) == 0)
h2 = set(h, "a", "b")
assertIsNot(self, h, h2)
@test (length(h) == 0)
@test (length(h2) == 1)
assertIsNone(self, get(h, "a"))
@test (get(h, "a", 42) == 42)
@test (get(h2, "a") == "b")
h3 = set(h2, "b", 10)
assertIsNot(self, h2, h3)
@test (length(h) == 0)
@test (length(h2) == 1)
@test (length(h3) == 2)
@test (get(h3, "a") == "b")
@test (get(h3, "b") == 10)
assertIsNone(self, get(h, "b"))
assertIsNone(self, get(h2, "b"))
assertIsNone(self, get(h, "a"))
@test (get(h2, "a") == "b")
h = nothing
h2 = nothing
h3 = nothing
end

function test_hamt_basics_3(self::HamtTest)
h = hamt()
o = object()
h1 = set(h, "1", o)
h2 = set(h1, "1", o)
assertIs(self, h1, h2)
end

function test_hamt_basics_4(self::HamtTest)
h = hamt()
h1 = set(h, "key", [])
h2 = set(h1, "key", [])
assertIsNot(self, h1, h2)
@test (length(h1) == 1)
@test (length(h2) == 1)
assertIsNot(self, get(h1, "key"), get(h2, "key"))
end

function test_hamt_collision_1(self::HamtTest)
k1 = HashKey(10, "aaa")
k2 = HashKey(10, "bbb")
k3 = HashKey(10, "ccc")
h = hamt()
h2 = set(h, k1, "a")
h3 = set(h2, k2, "b")
@test (get(h, k1) == nothing)
@test (get(h, k2) == nothing)
@test (get(h2, k1) == "a")
@test (get(h2, k2) == nothing)
@test (get(h3, k1) == "a")
@test (get(h3, k2) == "b")
h4 = set(h3, k2, "cc")
h5 = set(h4, k3, "aa")
@test (get(h3, k1) == "a")
@test (get(h3, k2) == "b")
@test (get(h4, k1) == "a")
@test (get(h4, k2) == "cc")
@test (get(h4, k3) == nothing)
@test (get(h5, k1) == "a")
@test (get(h5, k2) == "cc")
@test (get(h5, k2) == "cc")
@test (get(h5, k3) == "aa")
@test (length(h) == 0)
@test (length(h2) == 1)
@test (length(h3) == 2)
@test (length(h4) == 2)
@test (length(h5) == 3)
end

function test_hamt_stress(self::HamtTest)
COLLECTION_SIZE = 7000
TEST_ITERS_EVERY = 647
CRASH_HASH_EVERY = 97
CRASH_EQ_EVERY = 11
RUN_XTIMES = 3
for _ in 0:RUN_XTIMES - 1
h = hamt()
d = dict()
for i in 0:COLLECTION_SIZE - 1
key = KeyStr(i)
if !(i % CRASH_HASH_EVERY) != 0
HaskKeyCrasher(true) do 
assertRaises(self, HashingError) do 
set(h, key, i)
end
end
end
h = set(h, key, i)
if !(i % CRASH_EQ_EVERY) != 0
HaskKeyCrasher(true) do 
assertRaises(self, EqError) do 
get(h, KeyStr(i))
end
end
end
d[__add__(key, 1)] = i
@test (length(d) == length(h))
if !(i % TEST_ITERS_EVERY) != 0
@test (set(items(h)) == set(items(d)))
@test (length(items(h)) == length(items(d)))
end
end
@test (length(h) == COLLECTION_SIZE)
for key in 0:COLLECTION_SIZE - 1
@test (get(h, KeyStr(key), "not found") == key)
end
keys_to_delete = collect(0:COLLECTION_SIZE - 1)
shuffle(random, keys_to_delete)
for (iter_i, i) in enumerate(keys_to_delete)
key = KeyStr(i)
if !(iter_i % CRASH_HASH_EVERY) != 0
HaskKeyCrasher(true) do 
assertRaises(self, HashingError) do 
delete(h, key)
end
end
end
if !(iter_i % CRASH_EQ_EVERY) != 0
HaskKeyCrasher(true) do 
assertRaises(self, EqError) do 
delete(h, KeyStr(i))
end
end
end
h = delete(h, key)
@test (get(h, key, "not found") == "not found")
#Delete Unsupported
del(d)
@test (length(d) == length(h))
if iter_i == (COLLECTION_SIZE ÷ 2)
hm = h
dm = copy(d)
end
if !(iter_i % TEST_ITERS_EVERY) != 0
@test (set(keys(h)) == set(keys(d)))
@test (length(keys(h)) == length(keys(d)))
end
end
@test (length(d) == 0)
@test (length(h) == 0)
for key in dm
@test (get(hm, string(key)) == dm[key + 1])
end
@test (length(dm) == length(hm))
for (i, key) in enumerate(keys_to_delete)
hm = delete(hm, string(key))
@test (get(hm, string(key), "not found") == "not found")
pop(dm, string(key), nothing)
@test (length(d) == length(h))
if !(i % TEST_ITERS_EVERY) != 0
@test (set(values(h)) == set(values(d)))
@test (length(values(h)) == length(values(d)))
end
end
@test (length(d) == 0)
@test (length(h) == 0)
@test (collect(items(h)) == [])
end
end

function test_hamt_delete_1(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(102, "C")
D = HashKey(103, "D")
E = HashKey(104, "E")
Z = HashKey(-100, "Z")
Er = HashKey(103, "Er", D)
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
orig_len = length(h)
h = delete(h, C)
@test (length(h) == orig_len - 1)
assertRaisesRegex(self, ValueError, "cannot compare") do 
delete(h, Er)
end
h = delete(h, D)
@test (length(h) == orig_len - 2)
h2 = delete(h, Z)
assertIs(self, h2, h)
h = delete(h, A)
@test (length(h) == orig_len - 3)
@test (get(h, A, 42) == 42)
@test (get(h, B) == "b")
@test (get(h, E) == "e")
end

function test_hamt_delete_2(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(201001, "B")
C = HashKey(101001, "C")
D = HashKey(103, "D")
E = HashKey(104, "E")
Z = HashKey(-100, "Z")
Er = HashKey(201001, "Er", B)
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
orig_len = length(h)
assertRaisesRegex(self, ValueError, "cannot compare") do 
delete(h, Er)
end
h = delete(h, Z)
@test (length(h) == orig_len)
h = delete(h, C)
@test (length(h) == orig_len - 1)
h = delete(h, B)
@test (length(h) == orig_len - 2)
h = delete(h, A)
@test (length(h) == orig_len - 3)
@test (get(h, D) == "d")
@test (get(h, E) == "e")
h = delete(h, A)
h = delete(h, B)
h = delete(h, D)
h = delete(h, E)
@test (length(h) == 0)
end

function test_hamt_delete_3(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(100100, "C")
D = HashKey(100100, "D")
E = HashKey(104, "E")
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
orig_len = length(h)
h = delete(h, A)
@test (length(h) == orig_len - 1)
h = delete(h, E)
@test (length(h) == orig_len - 2)
@test (get(h, C) == "c")
@test (get(h, B) == "b")
end

function test_hamt_delete_4(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(100100, "C")
D = HashKey(100100, "D")
E = HashKey(100100, "E")
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
orig_len = length(h)
h = delete(h, D)
@test (length(h) == orig_len - 1)
h = delete(h, E)
@test (length(h) == orig_len - 2)
h = delete(h, C)
@test (length(h) == orig_len - 3)
h = delete(h, A)
@test (length(h) == orig_len - 4)
h = delete(h, B)
@test (length(h) == 0)
end

function test_hamt_delete_5(self::HamtTest)
h = hamt()
keys = []
for i in 0:16
key = HashKey(i, string(i))
push!(keys, key)
h = set(h, key, "val-$(i)")
end
collision_key16 = HashKey(16, "18")
h = set(h, collision_key16, "collision")
@test (length(h) == 18)
h = delete(h, keys[3])
@test (length(h) == 17)
h = delete(h, collision_key16)
@test (length(h) == 16)
h = delete(h, keys[17])
@test (length(h) == 15)
h = delete(h, keys[2])
@test (length(h) == 14)
h = delete(h, keys[2])
@test (length(h) == 14)
for key in keys
h = delete(h, key)
end
@test (length(h) == 0)
end

function test_hamt_items_1(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(201001, "B")
C = HashKey(101001, "C")
D = HashKey(103, "D")
E = HashKey(104, "E")
F = HashKey(110, "F")
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
h = set(h, F, "f")
it = items(h)
@test (set(collect(it)) == Set([(A, "a"), (B, "b"), (C, "c"), (D, "d"), (E, "e"), (F, "f")]))
end

function test_hamt_items_2(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(100100, "C")
D = HashKey(100100, "D")
E = HashKey(100100, "E")
F = HashKey(110, "F")
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
h = set(h, F, "f")
it = items(h)
@test (set(collect(it)) == Set([(A, "a"), (B, "b"), (C, "c"), (D, "d"), (E, "e"), (F, "f")]))
end

function test_hamt_keys_1(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(100100, "C")
D = HashKey(100100, "D")
E = HashKey(100100, "E")
F = HashKey(110, "F")
h = hamt()
h = set(h, A, "a")
h = set(h, B, "b")
h = set(h, C, "c")
h = set(h, D, "d")
h = set(h, E, "e")
h = set(h, F, "f")
@test (set(collect(keys(h))) == Set([A, B, C, D, E, F]))
@test (set(collect(h)) == Set([A, B, C, D, E, F]))
end

function test_hamt_items_3(self::HamtTest)
h = hamt()
@test (length(items(h)) == 0)
@test (collect(items(h)) == [])
end

function test_hamt_eq_1(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
C = HashKey(100100, "C")
D = HashKey(100100, "D")
E = HashKey(120, "E")
h1 = hamt()
h1 = set(h1, A, "a")
h1 = set(h1, B, "b")
h1 = set(h1, C, "c")
h1 = set(h1, D, "d")
h2 = hamt()
h2 = set(h2, A, "a")
@test !(h1 === h2)
@test h1 != h2
h2 = set(h2, B, "b")
@test !(h1 === h2)
@test h1 != h2
h2 = set(h2, C, "c")
@test !(h1 === h2)
@test h1 != h2
h2 = set(h2, D, "d2")
@test !(h1 === h2)
@test h1 != h2
h2 = set(h2, D, "d")
@test h1 === h2
@test !(h1 != h2)
h2 = set(h2, E, "e")
@test !(h1 === h2)
@test h1 != h2
h2 = delete(h2, D)
@test !(h1 === h2)
@test h1 != h2
h2 = set(h2, E, "d")
@test !(h1 === h2)
@test h1 != h2
end

function test_hamt_eq_2(self::HamtTest)
A = HashKey(100, "A")
Er = HashKey(100, "Er", A)
h1 = hamt()
h1 = set(h1, A, "a")
h2 = hamt()
h2 = set(h2, Er, "a")
assertRaisesRegex(self, ValueError, "cannot compare") do 
h1 === h2
end
assertRaisesRegex(self, ValueError, "cannot compare") do 
h1 != h2
end
end

function test_hamt_gc_1(self::HamtTest)
A = HashKey(100, "A")
h = hamt()
h = set(h, 0, 0)
ref = ref(weakref, h)
a = []
push!(a, a)
push!(a, h)
b = []
push!(a, b)
push!(b, a)
h = set(h, A, b)
#Delete Unsupported
del(b)
collect(gc)
collect(gc)
collect(gc)
assertIsNone(self, ref())
end

function test_hamt_gc_2(self::HamtTest)
A = HashKey(100, "A")
B = HashKey(101, "B")
h = hamt()
h = set(h, A, "a")
h = set(h, A, h)
ref = ref(weakref, h)
hi = items(h)
next(hi)
#Delete Unsupported
del(hi)
collect(gc)
collect(gc)
collect(gc)
assertIsNone(self, ref())
end

function test_hamt_in_1(self::HamtTest)
A = HashKey(100, "A")
AA = HashKey(100, "A")
B = HashKey(101, "B")
h = hamt()
h = set(h, A, 1)
@test A ∈ h
@test !(B ∈ h)
assertRaises(self, EqError) do 
HaskKeyCrasher(true) do 
AA ∈ h
end
end
assertRaises(self, HashingError) do 
HaskKeyCrasher(true) do 
AA ∈ h
end
end
end

function test_hamt_getitem_1(self::HamtTest)
A = HashKey(100, "A")
AA = HashKey(100, "A")
B = HashKey(101, "B")
h = hamt()
h = set(h, A, 1)
@test (h[__add__(A, 1)] == 1)
@test (h[__add__(AA, 1)] == 1)
assertRaises(self, KeyError) do 
h[__add__(B, 1)]
end
assertRaises(self, EqError) do 
HaskKeyCrasher(true) do 
h[__add__(AA, 1)]
end
end
assertRaises(self, HashingError) do 
HaskKeyCrasher(true) do 
h[__add__(AA, 1)]
end
end
end

function main()
context_test = ContextTest()
test_context_var_new_1(context_test)
test_context_var_repr_1(context_test)
test_context_subclassing_1(context_test)
test_context_new_1(context_test)
test_context_typerrors_1(context_test)
test_context_get_context_1(context_test)
test_context_run_1(context_test)
test_context_run_2(context_test)
test_context_run_3(context_test)
test_context_run_4(context_test)
test_context_run_5(context_test)
test_context_run_6(context_test)
test_context_run_7(context_test)
test_context_getset_1(context_test)
test_context_getset_2(context_test)
test_context_getset_3(context_test)
test_context_getset_4(context_test)
test_context_getset_5(context_test)
test_context_copy_1(context_test)
test_context_threads_1(context_test)
hamt_test = HamtTest()
test_hashkey_helper_1(hamt_test)
test_hamt_basics_1(hamt_test)
test_hamt_basics_2(hamt_test)
test_hamt_basics_3(hamt_test)
test_hamt_basics_4(hamt_test)
test_hamt_collision_1(hamt_test)
test_hamt_stress(hamt_test)
test_hamt_delete_1(hamt_test)
test_hamt_delete_2(hamt_test)
test_hamt_delete_3(hamt_test)
test_hamt_delete_4(hamt_test)
test_hamt_delete_5(hamt_test)
test_hamt_items_1(hamt_test)
test_hamt_items_2(hamt_test)
test_hamt_keys_1(hamt_test)
test_hamt_items_3(hamt_test)
test_hamt_eq_1(hamt_test)
test_hamt_eq_2(hamt_test)
test_hamt_gc_1(hamt_test)
test_hamt_gc_2(hamt_test)
test_hamt_in_1(hamt_test)
test_hamt_getitem_1(hamt_test)
end

main()