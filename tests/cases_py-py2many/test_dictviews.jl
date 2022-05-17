using Test

import copy



abstract type AbstractDictSetTest end
abstract type AbstractCustomSet <: Abstractset end
abstract type AbstractExc <: AbstractException end
abstract type AbstractBadEq end
mutable struct DictSetTest <: AbstractDictSetTest

end
function test_constructors_not_callable(self::DictSetTest)
kt = type_(keys(Dict()))
@test_throws TypeError kt(Dict())
@test_throws TypeError kt()
it = type_(items(Dict()))
@test_throws TypeError it(Dict())
@test_throws TypeError it()
vt = type_(values(Dict()))
@test_throws TypeError vt(Dict())
@test_throws TypeError vt()
end

function test_dict_keys(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
keys = keys(d)
@test (length(keys) == 2)
@test (set(keys) == Set([1, "a"]))
@test (keys == Set([1, "a"]))
assertNotEqual(self, keys, Set([1, "a", "b"]))
assertNotEqual(self, keys, Set([1, "b"]))
assertNotEqual(self, keys, Set([1]))
assertNotEqual(self, keys, 42)
assertIn(self, 1, keys)
assertIn(self, "a", keys)
assertNotIn(self, 10, keys)
assertNotIn(self, "Z", keys)
@test (keys(d) == keys(d))
e = Dict(1 => 11, "a" => "def")
@test (keys(d) == keys(e))
delete!(e, "a")
assertNotEqual(self, keys(d), keys(e))
end

function test_dict_items(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
items = items(d)
@test (length(items) == 2)
@test (set(items) == Set([(1, 10), ("a", "ABC")]))
@test (items == Set([(1, 10), ("a", "ABC")]))
assertNotEqual(self, items, Set([(1, 10), ("a", "ABC"), "junk"]))
assertNotEqual(self, items, Set([(1, 10), ("a", "def")]))
assertNotEqual(self, items, Set([(1, 10)]))
assertNotEqual(self, items, 42)
assertIn(self, (1, 10), items)
assertIn(self, ("a", "ABC"), items)
assertNotIn(self, (1, 11), items)
assertNotIn(self, 1, items)
assertNotIn(self, (), items)
assertNotIn(self, (1,), items)
assertNotIn(self, (1, 2, 3), items)
@test (items(d) == items(d))
e = copy(d)
@test (items(d) == items(e))
e["a"] = "def"
assertNotEqual(self, items(d), items(e))
end

function test_dict_mixed_keys_items(self::DictSetTest)
d = Dict((1, 1) => 11, (2, 2) => 22)
e = Dict(1 => 1, 2 => 2)
@test (keys(d) == items(e))
assertNotEqual(self, items(d), keys(e))
end

function test_dict_values(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
values = values(d)
@test (set(values) == Set([10, "ABC"]))
@test (length(values) == 2)
end

function test_dict_repr(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
@test isa(self, repr(d))
r = repr(items(d))
@test isa(self, r)
@test r == "dict_items([(\'a\', \'ABC\'), (1, 10)])" || r == "dict_items([(1, 10), (\'a\', \'ABC\')])"
r = repr(keys(d))
@test isa(self, r)
@test r == "dict_keys([\'a\', 1])" || r == "dict_keys([1, \'a\'])"
r = repr(values(d))
@test isa(self, r)
@test r == "dict_values([\'ABC\', 10])" || r == "dict_values([10, \'ABC\'])"
end

function test_keys_set_operations(self::CustomSet)
d1 = Dict("a" => 1, "b" => 2)
d2 = Dict("b" => 3, "c" => 2)
d3 = Dict("d" => 4, "e" => 5)
d4 = Dict("d" => 4)
mutable struct CustomSet <: AbstractCustomSet

end
function intersection(self::CustomSet, other)::CustomSet
return CustomSet(intersection(super(), other))
end

assertEqual(self, keys(d1) & keys(d1), Set(["a", "b"]))
assertEqual(self, keys(d1) & keys(d2), Set(["b"]))
assertEqual(self, keys(d1) & keys(d3), set())
assertEqual(self, keys(d1) & set(keys(d1)), Set(["a", "b"]))
assertEqual(self, keys(d1) & set(keys(d2)), Set(["b"]))
assertEqual(self, keys(d1) & set(keys(d3)), set())
assertEqual(self, keys(d1) & tuple(keys(d1)), Set(["a", "b"]))
assertEqual(self, keys(d3) & keys(d4), Set(["d"]))
assertEqual(self, keys(d4) & keys(d3), Set(["d"]))
assertEqual(self, keys(d4) & set(keys(d3)), Set(["d"]))
assertIsInstance(self, keys(d4) & frozenset(keys(d3)), set)
assertIsInstance(self, frozenset(keys(d3)) & keys(d4), set)
assertIs(self, type_(keys(d4) & CustomSet(keys(d3))), set)
assertIs(self, type_(keys(d1) & []), set)
assertIs(self, type_([] & keys(d1)), set)
assertEqual(self, keys(d1) | keys(d1), Set(["a", "b"]))
assertEqual(self, keys(d1) | keys(d2), Set(["a", "b", "c"]))
assertEqual(self, keys(d1) | keys(d3), Set(["a", "b", "d", "e"]))
assertEqual(self, keys(d1) | set(keys(d1)), Set(["a", "b"]))
assertEqual(self, keys(d1) | set(keys(d2)), Set(["a", "b", "c"]))
assertEqual(self, keys(d1) | set(keys(d3)), Set(["a", "b", "d", "e"]))
assertEqual(self, keys(d1) | (1, 2), Set(["a", "b", 1, 2]))
assertEqual(self, keys(d1)  ⊻  keys(d1), set())
assertEqual(self, keys(d1)  ⊻  keys(d2), Set(["a", "c"]))
assertEqual(self, keys(d1)  ⊻  keys(d3), Set(["a", "b", "d", "e"]))
assertEqual(self, keys(d1)  ⊻  set(keys(d1)), set())
assertEqual(self, keys(d1)  ⊻  set(keys(d2)), Set(["a", "c"]))
assertEqual(self, keys(d1)  ⊻  set(keys(d3)), Set(["a", "b", "d", "e"]))
assertEqual(self, keys(d1)  ⊻  tuple(keys(d2)), Set(["a", "c"]))
assertEqual(self, keys(d1) - keys(d1), set())
assertEqual(self, keys(d1) - keys(d2), Set(["a"]))
assertEqual(self, keys(d1) - keys(d3), Set(["a", "b"]))
assertEqual(self, keys(d1) - set(keys(d1)), set())
assertEqual(self, keys(d1) - set(keys(d2)), Set(["a"]))
assertEqual(self, keys(d1) - set(keys(d3)), Set(["a", "b"]))
assertEqual(self, keys(d1) - (0, 1), Set(["a", "b"]))
assertFalse(self, isdisjoint(keys(d1), keys(d1)))
assertFalse(self, isdisjoint(keys(d1), keys(d2)))
assertFalse(self, isdisjoint(keys(d1), collect(keys(d2))))
assertFalse(self, isdisjoint(keys(d1), set(keys(d2))))
assertTrue(self, isdisjoint(keys(d1), Set(["x", "y", "z"])))
assertTrue(self, isdisjoint(keys(d1), ["x", "y", "z"]))
assertTrue(self, isdisjoint(keys(d1), set(["x", "y", "z"])))
assertTrue(self, isdisjoint(keys(d1), set(["x", "y"])))
assertTrue(self, isdisjoint(keys(d1), ["x", "y"]))
assertTrue(self, isdisjoint(keys(d1), Dict()))
assertTrue(self, isdisjoint(keys(d1), keys(d3)))
de = Dict()
assertTrue(self, isdisjoint(keys(de), set()))
assertTrue(self, isdisjoint(keys(de), []))
assertTrue(self, isdisjoint(keys(de), keys(de)))
assertTrue(self, isdisjoint(keys(de), [1]))
end

function test_items_set_operations(self::DictSetTest)
d1 = Dict("a" => 1, "b" => 2)
d2 = Dict("a" => 2, "b" => 2)
d3 = Dict("d" => 4, "e" => 5)
@test (items(d1) & items(d1) == Set([("a", 1), ("b", 2)]))
@test (items(d1) & items(d2) == Set([("b", 2)]))
@test (items(d1) & items(d3) == set())
@test (items(d1) & set(items(d1)) == Set([("a", 1), ("b", 2)]))
@test (items(d1) & set(items(d2)) == Set([("b", 2)]))
@test (items(d1) & set(items(d3)) == set())
@test (items(d1) | items(d1) == Set([("a", 1), ("b", 2)]))
@test (items(d1) | items(d2) == Set([("a", 1), ("a", 2), ("b", 2)]))
@test (items(d1) | items(d3) == Set([("a", 1), ("b", 2), ("d", 4), ("e", 5)]))
@test (items(d1) | set(items(d1)) == Set([("a", 1), ("b", 2)]))
@test (items(d1) | set(items(d2)) == Set([("a", 1), ("a", 2), ("b", 2)]))
@test (items(d1) | set(items(d3)) == Set([("a", 1), ("b", 2), ("d", 4), ("e", 5)]))
@test (items(d1)  ⊻  items(d1) == set())
@test (items(d1)  ⊻  items(d2) == Set([("a", 1), ("a", 2)]))
@test (items(d1)  ⊻  items(d3) == Set([("a", 1), ("b", 2), ("d", 4), ("e", 5)]))
@test (items(d1) - items(d1) == set())
@test (items(d1) - items(d2) == Set([("a", 1)]))
@test (items(d1) - items(d3) == Set([("a", 1), ("b", 2)]))
@test (items(d1) - set(items(d1)) == set())
@test (items(d1) - set(items(d2)) == Set([("a", 1)]))
@test (items(d1) - set(items(d3)) == Set([("a", 1), ("b", 2)]))
@test !(isdisjoint(items(d1), items(d1)))
@test !(isdisjoint(items(d1), items(d2)))
@test !(isdisjoint(items(d1), collect(items(d2))))
@test !(isdisjoint(items(d1), set(items(d2))))
@test isdisjoint(items(d1), Set(["x", "y", "z"]))
@test isdisjoint(items(d1), ["x", "y", "z"])
@test isdisjoint(items(d1), set(["x", "y", "z"]))
@test isdisjoint(items(d1), set(["x", "y"]))
@test isdisjoint(items(d1), Dict())
@test isdisjoint(items(d1), items(d3))
de = Dict()
@test isdisjoint(items(de), set())
@test isdisjoint(items(de), [])
@test isdisjoint(items(de), items(de))
@test isdisjoint(items(de), [1])
end

function test_set_operations_with_iterator(self::DictSetTest)
origin = Dict(1 => 2, 3 => 4)
@test (keys(origin) & (x for x in [1, 2]) == Set([1]))
@test (keys(origin) | (x for x in [1, 2]) == Set([1, 2, 3]))
@test (keys(origin)  ⊻  (x for x in [1, 2]) == Set([2, 3]))
@test (keys(origin) - (x for x in [1, 2]) == Set([3]))
items = items(origin)
@test (items & (x for x in [(1, 2)]) == Set([(1, 2)]))
@test (items  ⊻  (x for x in [(1, 2)]) == Set([(3, 4)]))
@test (items | (x for x in [(1, 2)]) == Set([(1, 2), (3, 4)]))
@test (items - (x for x in [(1, 2)]) == Set([(3, 4)]))
end

function test_set_operations_with_noniterable(self::DictSetTest)
assertRaises(self, TypeError) do 
keys(Dict()) & 1
end
assertRaises(self, TypeError) do 
keys(Dict()) | 1
end
assertRaises(self, TypeError) do 
keys(Dict())  ⊻  1
end
assertRaises(self, TypeError) do 
keys(Dict()) - 1
end
assertRaises(self, TypeError) do 
items(Dict()) & 1
end
assertRaises(self, TypeError) do 
items(Dict()) | 1
end
assertRaises(self, TypeError) do 
items(Dict())  ⊻  1
end
assertRaises(self, TypeError) do 
items(Dict()) - 1
end
end

function test_recursive_repr(self::DictSetTest)
d = Dict()
d[42] = values(d)
r = repr(d)
@test isa(self, r)
d[42] = items(d)
r = repr(d)
@test isa(self, r)
end

function test_deeply_nested_repr(self::DictSetTest)
d = Dict()
for i in 0:getrecursionlimit(sys) + 99
d = Dict(42 => values(d))
end
@test_throws RecursionError repr(d)
end

function test_copy(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
@test_throws TypeError copy.copy(keys(d))
@test_throws TypeError copy.copy(values(d))
@test_throws TypeError copy.copy(items(d))
end

function test_compare_error(self::BadEq)
mutable struct Exc <: AbstractExc

end

mutable struct BadEq <: AbstractBadEq

end
function __hash__(self::BadEq)::Int64
return 7
end

function __eq__(self::BadEq, other)
throw(Exc)
end

k1, k2 = (BadEq(), BadEq())
v1, v2 = (BadEq(), BadEq())
d = Dict(k1 => v1)
assertIn(self, k1, d)
assertIn(self, k1, keys(d))
assertIn(self, v1, values(d))
assertIn(self, (k1, v1), items(d))
assertRaises(self, Exc, d.__contains__, k2)
assertRaises(self, Exc, keys(d).__contains__, k2)
assertRaises(self, Exc, items(d).__contains__, (k2, v1))
assertRaises(self, Exc, items(d).__contains__, (k1, v2))
assertRaises(self, Exc) do 
v2 ∈ values(d)
end
end

function test_pickle(self::DictSetTest)
d = Dict(1 => 10, "a" => "ABC")
for proto in 0:pickle.HIGHEST_PROTOCOL
@test_throws (TypeError, pickle.PicklingError) pickle.dumps(keys(d), proto)
@test_throws (TypeError, pickle.PicklingError) pickle.dumps(values(d), proto)
@test_throws (TypeError, pickle.PicklingError) pickle.dumps(items(d), proto)
end
end

function test_abc_registry(self::DictSetTest)
d = dict(1)
@test isa(self, keys(d))
@test isa(self, keys(d))
@test isa(self, keys(d))
@test isa(self, keys(d))
@test isa(self, keys(d))
@test isa(self, keys(d))
@test isa(self, values(d))
@test isa(self, values(d))
@test isa(self, values(d))
@test isa(self, items(d))
@test isa(self, items(d))
@test isa(self, items(d))
@test isa(self, items(d))
@test isa(self, items(d))
@test isa(self, items(d))
end

function main()
dict_set_test = DictSetTest()
test_constructors_not_callable(dict_set_test)
test_dict_keys(dict_set_test)
test_dict_items(dict_set_test)
test_dict_mixed_keys_items(dict_set_test)
test_dict_values(dict_set_test)
test_dict_repr(dict_set_test)
test_keys_set_operations(dict_set_test)
test_items_set_operations(dict_set_test)
test_set_operations_with_iterator(dict_set_test)
test_set_operations_with_noniterable(dict_set_test)
test_recursive_repr(dict_set_test)
test_deeply_nested_repr(dict_set_test)
test_copy(dict_set_test)
test_compare_error(dict_set_test)
test_pickle(dict_set_test)
test_abc_registry(dict_set_test)
end

main()