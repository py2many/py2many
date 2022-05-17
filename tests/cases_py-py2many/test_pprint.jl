using Test


import io

import pprint
import random




abstract type Abstractlist2 <: Abstractlist end
abstract type Abstractlist3 <: Abstractlist end
abstract type Abstractlist_custom_repr <: Abstractlist end
abstract type Abstracttuple2 <: Abstracttuple end
abstract type Abstracttuple3 <: Abstracttuple end
abstract type Abstracttuple_custom_repr <: Abstracttuple end
abstract type Abstractset2 <: Abstractset end
abstract type Abstractset3 <: Abstractset end
abstract type Abstractset_custom_repr <: Abstractset end
abstract type Abstractfrozenset2 <: Abstractfrozenset end
abstract type Abstractfrozenset3 <: Abstractfrozenset end
abstract type Abstractfrozenset_custom_repr <: Abstractfrozenset end
abstract type Abstractdict2 <: Abstractdict end
abstract type Abstractdict3 <: Abstractdict end
abstract type Abstractdict_custom_repr <: Abstractdict end
abstract type Abstractdataclass1 end
abstract type Abstractdataclass2 end
abstract type Abstractdataclass3 end
abstract type Abstractdataclass4 end
abstract type Abstractdataclass5 end
abstract type Abstractdataclass6 end
abstract type AbstractUnorderable end
abstract type AbstractOrderable end
abstract type AbstractQueryTestCase end
abstract type AbstractTemperature <: Abstractint end
abstract type AbstractAdvancedNamespace end
abstract type AbstractDottedPrettyPrinter <: Abstractpprint.PrettyPrinter end
mutable struct list2 <: Abstractlist2

end

mutable struct list3 <: Abstractlist3

end
function __repr__(self::list3)
return __repr__(list)
end

mutable struct list_custom_repr <: Abstractlist_custom_repr

end
function __repr__(self::list_custom_repr)::String
return repeat("*",length(__repr__(list)))
end

mutable struct tuple2 <: Abstracttuple2

end

mutable struct tuple3 <: Abstracttuple3

end
function __repr__(self::tuple3)
return __repr__(tuple)
end

mutable struct tuple_custom_repr <: Abstracttuple_custom_repr

end
function __repr__(self::tuple_custom_repr)::String
return repeat("*",length(__repr__(tuple)))
end

mutable struct set2 <: Abstractset2

end

mutable struct set3 <: Abstractset3

end
function __repr__(self::set3)
return __repr__(set)
end

mutable struct set_custom_repr <: Abstractset_custom_repr

end
function __repr__(self::set_custom_repr)::String
return repeat("*",length(__repr__(set)))
end

mutable struct frozenset2 <: Abstractfrozenset2

end

mutable struct frozenset3 <: Abstractfrozenset3

end
function __repr__(self::frozenset3)
return __repr__(frozenset)
end

mutable struct frozenset_custom_repr <: Abstractfrozenset_custom_repr

end
function __repr__(self::frozenset_custom_repr)::String
return repeat("*",length(__repr__(frozenset)))
end

mutable struct dict2 <: Abstractdict2

end

mutable struct dict3 <: Abstractdict3

end
function __repr__(self::dict3)
return __repr__(dict)
end

mutable struct dict_custom_repr <: Abstractdict_custom_repr

end
function __repr__(self::dict_custom_repr)::String
return repeat("*",length(__repr__(dict)))
end

mutable struct dataclass1 <: Abstractdataclass1
field1::String
field2::Int64
field3::Bool
field4::Int64

                    dataclass1(field1::String, field2::Int64, field3::Bool = false, field4::Int64 = field(dataclasses, 1, false)) =
                        new(field1, field2, field3, field4)
end

mutable struct dataclass2 <: Abstractdataclass2
a::Int64

                    dataclass2(a::Int64 = 1) =
                        new(a)
end
function __repr__(self::dataclass2)::String
return "custom repr that doesn\'t fit within pprint width"
end

mutable struct dataclass3 <: Abstractdataclass3
a::Int64

                    dataclass3(a::Int64 = 1) =
                        new(a)
end

mutable struct dataclass4 <: Abstractdataclass4
a::Abstractdataclass4
b::Int64

                    dataclass4(a::Abstractdataclass4, b::Int64 = 1) =
                        new(a, b)
end

mutable struct dataclass5 <: Abstractdataclass5
a::Abstractdataclass6
b::Int64

                    dataclass5(a::Abstractdataclass6, b::Int64 = 1) =
                        new(a, b)
end

mutable struct dataclass6 <: Abstractdataclass6
c::Abstractdataclass5
d::Int64

                    dataclass6(c::Abstractdataclass5, d::Int64 = 1) =
                        new(c, d)
end

mutable struct Unorderable <: AbstractUnorderable

end
function __repr__(self::Unorderable)::String
return string(id(self))
end

mutable struct Orderable <: AbstractOrderable
_hash
end
function __lt__(self::Orderable, other)::Bool
return false
end

function __gt__(self::Orderable, other)::Bool
return self != other
end

function __le__(self::Orderable, other)::Bool
return self == other
end

function __ge__(self::Orderable, other)::Bool
return true
end

function __eq__(self::Orderable, other)::Bool
return self == other
end

function __ne__(self::Orderable, other)::Bool
return self != other
end

function __hash__(self::Orderable)
return self._hash
end

mutable struct QueryTestCase <: AbstractQueryTestCase
a
b
d
assertTrue
end
function setUp(self::QueryTestCase)
self.a = collect(0:99)
self.b = collect(0:199)
self.a[end - -10] = self.b
end

function test_init(self::QueryTestCase)
pp = PrettyPrinter(pprint)
pp = PrettyPrinter(pprint, 4, 40, 5, StringIO(io), true)
pp = PrettyPrinter(pprint, 4, 40, 5, StringIO(io))
pp = PrettyPrinter(pprint, false)
assertRaises(self, TypeError) do 
pp = PrettyPrinter(pprint, 4, 40, 5, StringIO(io), true)
end
@test_throws ValueError pprint.PrettyPrinter(-1)
@test_throws ValueError pprint.PrettyPrinter(0)
@test_throws ValueError pprint.PrettyPrinter(-1)
@test_throws ValueError pprint.PrettyPrinter(0)
end

function test_basic(self::QueryTestCase)
pp = PrettyPrinter(pprint)
for safe in (2, 2.0, 2im, "abc", [3], (2, 2), Dict(3 => 3), b"def", Vector{UInt8}(b"ghi"), true, false, nothing, ..., self.a, self.b)
@test !(isrecursive(pprint, safe))
@test isreadable(pprint, safe)
@test !(isrecursive(pp, safe))
@test isreadable(pp, safe)
end
end

function test_knotted(self::QueryTestCase)
self.b[68] = self.a
self.d = Dict()
self.d[1] = self.d
self.d[2] = self.d
self.d[3] = self.d
pp = PrettyPrinter(pprint)
for icky in (self.a, self.b, self.d, (self.d, self.d))
@test isrecursive(pprint, icky)
@test !(isreadable(pprint, icky))
@test isrecursive(pp, icky)
@test !(isreadable(pp, icky))
end
clear(self.d)
#Delete Unsupported
del(self.a)
#Delete Unsupported
del(self.b)
for safe in (self.a, self.b, self.d, (self.d, self.d))
@test !(isrecursive(pprint, safe))
@test isreadable(pprint, safe)
@test !(isrecursive(pp, safe))
@test isreadable(pp, safe)
end
end

function test_unreadable(self::QueryTestCase)
pp = PrettyPrinter(pprint)
for unreadable in (type_(3), pprint, pprint.isrecursive)
@test !(isrecursive(pprint, unreadable))
@test !(isreadable(pprint, unreadable))
@test !(isrecursive(pp, unreadable))
@test !(isreadable(pp, unreadable))
end
end

function test_same_as_repr(self::QueryTestCase)
for simple in (0, 0, 0 + 0im, 0.0, "", b"", Vector{UInt8}(), (), tuple2(), tuple3(), [], list2(), list3(), set(), set2(), set3(), frozenset(), frozenset2(), frozenset3(), Dict(), dict2(), dict3(), self.assertTrue, pprint, -6, -6, -6 - 6im, -1.5, "x", b"x", Vector{UInt8}(b"x"), (3,), [3], Dict(3 => 6), (1, 2), [3, 4], Dict(5 => 6), tuple2((1, 2)), tuple3((1, 2)), tuple3(0:99), [3, 4], list2([3, 4]), list3([3, 4]), list3(0:99), set(Set([7])), set2(Set([7])), set3(Set([7])), frozenset(Set([8])), frozenset2(Set([8])), frozenset3(Set([8])), dict2(Dict(5 => 6)), dict3(Dict(5 => 6)), -10:-1:10, true, false, nothing, ...)
native = repr(simple)
@test (pformat(pprint, simple) == native)
@test (replace(pformat(pprint, simple, 1, 0), "\n", " ") == native)
@test (pformat(pprint, simple, true) == native)
@test (saferepr(pprint, simple) == native)
end
end

function test_container_repr_override_called(self::QueryTestCase)
N = 1000
for cont in (list_custom_repr(), list_custom_repr([1, 2, 3]), list_custom_repr(0:N - 1), tuple_custom_repr(), tuple_custom_repr([1, 2, 3]), tuple_custom_repr(0:N - 1), set_custom_repr(), set_custom_repr([1, 2, 3]), set_custom_repr(0:N - 1), frozenset_custom_repr(), frozenset_custom_repr([1, 2, 3]), frozenset_custom_repr(0:N - 1), dict_custom_repr(), dict_custom_repr(Dict(5 => 6)), dict_custom_repr(zip(0:N - 1, 0:N - 1)))
native = repr(cont)
expected = repeat("*",length(native))
@test (pformat(pprint, cont) == expected)
@test (pformat(pprint, cont, 1, 0) == expected)
@test (saferepr(pprint, cont) == expected)
end
end

function test_basic_line_wrap(self::QueryTestCase)
o = Dict("RPM_cal" => 0, "RPM_cal2" => 48059, "Speed_cal" => 0, "controldesk_runtime_us" => 0, "main_code_runtime_us" => 0, "read_io_runtime_us" => 0, "write_io_runtime_us" => 43690)
exp = "{\'RPM_cal\': 0,\n \'RPM_cal2\': 48059,\n \'Speed_cal\': 0,\n \'controldesk_runtime_us\': 0,\n \'main_code_runtime_us\': 0,\n \'read_io_runtime_us\': 0,\n \'write_io_runtime_us\': 43690}"
for type_ in [dict, dict2]
@test (pformat(pprint, type_(o)) == exp)
end
o = 0:99
exp = "[%s]" % join(map(str, o), ",\n ")
for type_ in [list, list2]
@test (pformat(pprint, type_(o)) == exp)
end
o = tuple(0:99)
exp = "(%s)" % join(map(str, o), ",\n ")
for type_ in [tuple, tuple2]
@test (pformat(pprint, type_(o)) == exp)
end
o = 0:99
exp = "[   %s]" % join(map(str, o), ",\n    ")
for type_ in [list, list2]
@test (pformat(pprint, type_(o), 4) == exp)
end
end

function test_nested_indentations(self::QueryTestCase)
o1 = collect(0:9)
o2 = dict(1, 2, 3)
o = [o1, o2]
expected = "[   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],\n    {\'first\': 1, \'second\': 2, \'third\': 3}]"
@test (pformat(pprint, o, 4, 42) == expected)
expected = "[   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],\n    {   \'first\': 1,\n        \'second\': 2,\n        \'third\': 3}]"
@test (pformat(pprint, o, 4, 41) == expected)
end

function test_width(self::QueryTestCase)
expected = "[[[[[[1, 2, 3],\n     \'1 2\']]]],\n {1: [1, 2, 3],\n  2: [12, 34]},\n \'abc def ghi\',\n (\'ab cd ef\',),\n set2({1, 23}),\n [[[[[1, 2, 3],\n     \'1 2\']]]]]"
o = eval(expected)
@test (pformat(pprint, o, 15) == expected)
@test (pformat(pprint, o, 16) == expected)
@test (pformat(pprint, o, 25) == expected)
@test (pformat(pprint, o, 14) == "[[[[[[1,\n      2,\n      3],\n     \'1 \'\n     \'2\']]]],\n {1: [1,\n      2,\n      3],\n  2: [12,\n      34]},\n \'abc def \'\n \'ghi\',\n (\'ab cd \'\n  \'ef\',),\n set2({1,\n       23}),\n [[[[[1,\n      2,\n      3],\n     \'1 \'\n     \'2\']]]]]")
end

function test_integer(self::Temperature)
assertEqual(self, pformat(pprint, 1234567), "1234567")
assertEqual(self, pformat(pprint, 1234567, true), "1_234_567")
mutable struct Temperature <: AbstractTemperature

end
function __new__(cls, celsius_degrees)
return __new__(super(), Temperature)
end

function __repr__(self::Temperature)
kelvin_degrees = self + 273.15
return "$(kelvin_degrees)°K"
end

assertEqual(self, pformat(pprint, Temperature(1000)), "1273.15°K")
end

function test_sorted_dict(self::QueryTestCase)
d = Dict("a" => 1, "b" => 1, "c" => 1)
@test (pformat(pprint, d) == "{\'a\': 1, \'b\': 1, \'c\': 1}")
@test (pformat(pprint, [d, d]) == "[{\'a\': 1, \'b\': 1, \'c\': 1}, {\'a\': 1, \'b\': 1, \'c\': 1}]")
@test (pformat(pprint, Dict("xy\tab\n" => (3,), 5 => [[]], () => Dict())) == "{5: [[]], \'xy\\tab\\n\': (3,), (): {}}")
end

function test_sort_dict(self::QueryTestCase)
d = fromkeys(dict, "cba")
@test (pformat(pprint, d, false) == "{\'c\': None, \'b\': None, \'a\': None}")
@test (pformat(pprint, [d, d], false) == "[{\'c\': None, \'b\': None, \'a\': None}, {\'c\': None, \'b\': None, \'a\': None}]")
end

function test_ordered_dict(self::QueryTestCase)
d = OrderedDict(collections)
@test (pformat(pprint, d, 1) == "OrderedDict()")
d = OrderedDict(collections, [])
@test (pformat(pprint, d, 1) == "OrderedDict()")
words = split("the quick brown fox jumped over a lazy dog")
d = OrderedDict(collections, zip(words, count(itertools)))
@test (pformat(pprint, d) == "OrderedDict([(\'the\', 0),\n             (\'quick\', 1),\n             (\'brown\', 2),\n             (\'fox\', 3),\n             (\'jumped\', 4),\n             (\'over\', 5),\n             (\'a\', 6),\n             (\'lazy\', 7),\n             (\'dog\', 8)])")
end

function test_mapping_proxy(self::QueryTestCase)
words = split("the quick brown fox jumped over a lazy dog")
d = dict(zip(words, count(itertools)))
m = MappingProxyType(types, d)
@test (pformat(pprint, m) == "mappingproxy({\'a\': 6,\n              \'brown\': 2,\n              \'dog\': 8,\n              \'fox\': 3,\n              \'jumped\': 4,\n              \'lazy\': 7,\n              \'over\': 5,\n              \'quick\': 1,\n              \'the\': 0})")
d = OrderedDict(collections, zip(words, count(itertools)))
m = MappingProxyType(types, d)
@test (pformat(pprint, m) == "mappingproxy(OrderedDict([(\'the\', 0),\n                          (\'quick\', 1),\n                          (\'brown\', 2),\n                          (\'fox\', 3),\n                          (\'jumped\', 4),\n                          (\'over\', 5),\n                          (\'a\', 6),\n                          (\'lazy\', 7),\n                          (\'dog\', 8)]))")
end

function test_empty_simple_namespace(self::QueryTestCase)
ns = SimpleNamespace(types)
formatted = pformat(pprint, ns)
@test (formatted == "namespace()")
end

function test_small_simple_namespace(self::QueryTestCase)
ns = SimpleNamespace(types, 1, 2)
formatted = pformat(pprint, ns)
@test (formatted == "namespace(a=1, b=2)")
end

function test_simple_namespace(self::QueryTestCase)
ns = SimpleNamespace(types, 0, 1, 2, 3, 4, 5, 6, 7, 8)
formatted = pformat(pprint, ns, 60, 4)
@test (formatted == "namespace(the=0,\n          quick=1,\n          brown=2,\n          fox=3,\n          jumped=4,\n          over=5,\n          a=6,\n          lazy=7,\n          dog=8)")
end

function test_simple_namespace_subclass(self::AdvancedNamespace)
mutable struct AdvancedNamespace <: AbstractAdvancedNamespace

end

ns = AdvancedNamespace(0, 1, 2, 3, 4, 5, 6, 7, 8)
formatted = pformat(pprint, ns, 60)
assertEqual(self, formatted, "AdvancedNamespace(the=0,\n                  quick=1,\n                  brown=2,\n                  fox=3,\n                  jumped=4,\n                  over=5,\n                  a=6,\n                  lazy=7,\n                  dog=8)")
end

function test_empty_dataclass(self::QueryTestCase)
dc = make_dataclass(dataclasses, "MyDataclass", ())()
formatted = pformat(pprint, dc)
@test (formatted == "MyDataclass()")
end

function test_small_dataclass(self::QueryTestCase)
dc = dataclass1("text", 123)
formatted = pformat(pprint, dc)
@test (formatted == "dataclass1(field1=\'text\', field2=123, field3=False)")
end

function test_larger_dataclass(self::QueryTestCase)
dc = dataclass1("some fairly long text", Int(floor(10000000000.0)), true)
formatted = pformat(pprint, [dc, dc], 60, 4)
@test (formatted == "[   dataclass1(field1=\'some fairly long text\',\n               field2=10000000000,\n               field3=True),\n    dataclass1(field1=\'some fairly long text\',\n               field2=10000000000,\n               field3=True)]")
end

function test_dataclass_with_repr(self::QueryTestCase)
dc = dataclass2()
formatted = pformat(pprint, dc, 20)
@test (formatted == "custom repr that doesn\'t fit within pprint width")
end

function test_dataclass_no_repr(self::QueryTestCase)
dc = dataclass3()
formatted = pformat(pprint, dc, 10)
assertRegex(self, formatted, "<test.test_pprint.dataclass3 object at \\w+>")
end

function test_recursive_dataclass(self::QueryTestCase)
dc = dataclass4(nothing)
dc.a = dc
formatted = pformat(pprint, dc, 10)
@test (formatted == "dataclass4(a=...,\n           b=1)")
end

function test_cyclic_dataclass(self::QueryTestCase)
dc5 = dataclass5(nothing)
dc6 = dataclass6(nothing)
dc5.a = dc6
dc6.c = dc5
formatted = pformat(pprint, dc5, 10)
@test (formatted == "dataclass5(a=dataclass6(c=...,\n                        d=1),\n           b=1)")
end

function test_subclassing(self::QueryTestCase)
o = Dict("names with spaces" => "should be presented using repr()", "others.should.not.be" => "like.this")
exp = "{\'names with spaces\': \'should be presented using repr()\',\n others.should.not.be: like.this}"
dotted_printer = DottedPrettyPrinter()
@test (pformat(dotted_printer, o) == exp)
o1 = ["with space"]
exp1 = "[\'with space\']"
@test (pformat(dotted_printer, o1) == exp1)
o2 = ["without.space"]
exp2 = "[without.space]"
@test (pformat(dotted_printer, o2) == exp2)
end

function test_set_reprs(self::QueryTestCase)
@test (pformat(pprint, set()) == "set()")
@test (pformat(pprint, set(0:2)) == "{0, 1, 2}")
@test (pformat(pprint, set(0:6), 20) == "{0,\n 1,\n 2,\n 3,\n 4,\n 5,\n 6}")
@test (pformat(pprint, set2(0:6), 20) == "set2({0,\n      1,\n      2,\n      3,\n      4,\n      5,\n      6})")
@test (pformat(pprint, set3(0:6), 20) == "set3({0, 1, 2, 3, 4, 5, 6})")
@test (pformat(pprint, frozenset()) == "frozenset()")
@test (pformat(pprint, frozenset(0:2)) == "frozenset({0, 1, 2})")
@test (pformat(pprint, frozenset(0:6), 20) == "frozenset({0,\n           1,\n           2,\n           3,\n           4,\n           5,\n           6})")
@test (pformat(pprint, frozenset2(0:6), 20) == "frozenset2({0,\n            1,\n            2,\n            3,\n            4,\n            5,\n            6})")
@test (pformat(pprint, frozenset3(0:6), 20) == "frozenset3({0, 1, 2, 3, 4, 5, 6})")
end

function test_set_of_sets_reprs(self::QueryTestCase)
cube_repr_tgt = "{frozenset(): frozenset({frozenset({2}), frozenset({0}), frozenset({1})}),\n frozenset({0}): frozenset({frozenset(),\n                            frozenset({0, 2}),\n                            frozenset({0, 1})}),\n frozenset({1}): frozenset({frozenset(),\n                            frozenset({1, 2}),\n                            frozenset({0, 1})}),\n frozenset({2}): frozenset({frozenset(),\n                            frozenset({1, 2}),\n                            frozenset({0, 2})}),\n frozenset({1, 2}): frozenset({frozenset({2}),\n                               frozenset({1}),\n                               frozenset({0, 1, 2})}),\n frozenset({0, 2}): frozenset({frozenset({2}),\n                               frozenset({0}),\n                               frozenset({0, 1, 2})}),\n frozenset({0, 1}): frozenset({frozenset({0}),\n                               frozenset({1}),\n                               frozenset({0, 1, 2})}),\n frozenset({0, 1, 2}): frozenset({frozenset({1, 2}),\n                                  frozenset({0, 2}),\n                                  frozenset({0, 1})})}"
cube = cube(test.test_set, 3)
@test (pformat(pprint, cube) == cube_repr_tgt)
cubo_repr_tgt = "{frozenset({frozenset({0, 2}), frozenset({0})}): frozenset({frozenset({frozenset({0,\n                                                                                  2}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({0}),\n                                                                       frozenset({0,\n                                                                                  1})}),\n                                                            frozenset({frozenset(),\n                                                                       frozenset({0})}),\n                                                            frozenset({frozenset({2}),\n                                                                       frozenset({0,\n                                                                                  2})})}),\n frozenset({frozenset({0, 1}), frozenset({1})}): frozenset({frozenset({frozenset({0,\n                                                                                  1}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({0}),\n                                                                       frozenset({0,\n                                                                                  1})}),\n                                                            frozenset({frozenset({1}),\n                                                                       frozenset({1,\n                                                                                  2})}),\n                                                            frozenset({frozenset(),\n                                                                       frozenset({1})})}),\n frozenset({frozenset({1, 2}), frozenset({1})}): frozenset({frozenset({frozenset({1,\n                                                                                  2}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({2}),\n                                                                       frozenset({1,\n                                                                                  2})}),\n                                                            frozenset({frozenset(),\n                                                                       frozenset({1})}),\n                                                            frozenset({frozenset({1}),\n                                                                       frozenset({0,\n                                                                                  1})})}),\n frozenset({frozenset({1, 2}), frozenset({2})}): frozenset({frozenset({frozenset({1,\n                                                                                  2}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({1}),\n                                                                       frozenset({1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({2}),\n                                                                       frozenset({0,\n                                                                                  2})}),\n                                                            frozenset({frozenset(),\n                                                                       frozenset({2})})}),\n frozenset({frozenset(), frozenset({0})}): frozenset({frozenset({frozenset({0}),\n                                                                 frozenset({0,\n                                                                            1})}),\n                                                      frozenset({frozenset({0}),\n                                                                 frozenset({0,\n                                                                            2})}),\n                                                      frozenset({frozenset(),\n                                                                 frozenset({1})}),\n                                                      frozenset({frozenset(),\n                                                                 frozenset({2})})}),\n frozenset({frozenset(), frozenset({1})}): frozenset({frozenset({frozenset(),\n                                                                 frozenset({0})}),\n                                                      frozenset({frozenset({1}),\n                                                                 frozenset({1,\n                                                                            2})}),\n                                                      frozenset({frozenset(),\n                                                                 frozenset({2})}),\n                                                      frozenset({frozenset({1}),\n                                                                 frozenset({0,\n                                                                            1})})}),\n frozenset({frozenset({2}), frozenset()}): frozenset({frozenset({frozenset({2}),\n                                                                 frozenset({1,\n                                                                            2})}),\n                                                      frozenset({frozenset(),\n                                                                 frozenset({0})}),\n                                                      frozenset({frozenset(),\n                                                                 frozenset({1})}),\n                                                      frozenset({frozenset({2}),\n                                                                 frozenset({0,\n                                                                            2})})}),\n frozenset({frozenset({0, 1, 2}), frozenset({0, 1})}): frozenset({frozenset({frozenset({1,\n                                                                                        2}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({0,\n                                                                                        2}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({0}),\n                                                                             frozenset({0,\n                                                                                        1})}),\n                                                                  frozenset({frozenset({1}),\n                                                                             frozenset({0,\n                                                                                        1})})}),\n frozenset({frozenset({0}), frozenset({0, 1})}): frozenset({frozenset({frozenset(),\n                                                                       frozenset({0})}),\n                                                            frozenset({frozenset({0,\n                                                                                  1}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({0}),\n                                                                       frozenset({0,\n                                                                                  2})}),\n                                                            frozenset({frozenset({1}),\n                                                                       frozenset({0,\n                                                                                  1})})}),\n frozenset({frozenset({2}), frozenset({0, 2})}): frozenset({frozenset({frozenset({0,\n                                                                                  2}),\n                                                                       frozenset({0,\n                                                                                  1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({2}),\n                                                                       frozenset({1,\n                                                                                  2})}),\n                                                            frozenset({frozenset({0}),\n                                                                       frozenset({0,\n                                                                                  2})}),\n                                                            frozenset({frozenset(),\n                                                                       frozenset({2})})}),\n frozenset({frozenset({0, 1, 2}), frozenset({0, 2})}): frozenset({frozenset({frozenset({1,\n                                                                                        2}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({0,\n                                                                                        1}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({0}),\n                                                                             frozenset({0,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({2}),\n                                                                             frozenset({0,\n                                                                                        2})})}),\n frozenset({frozenset({1, 2}), frozenset({0, 1, 2})}): frozenset({frozenset({frozenset({0,\n                                                                                        2}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({0,\n                                                                                        1}),\n                                                                             frozenset({0,\n                                                                                        1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({2}),\n                                                                             frozenset({1,\n                                                                                        2})}),\n                                                                  frozenset({frozenset({1}),\n                                                                             frozenset({1,\n                                                                                        2})})})}"
cubo = linegraph(test.test_set, cube)
@test (pformat(pprint, cubo) == cubo_repr_tgt)
end

function test_depth(self::QueryTestCase)
nested_tuple = (1, (2, (3, (4, (5, 6)))))
nested_dict = Dict(1 => Dict(2 => Dict(3 => Dict(4 => Dict(5 => Dict(6 => 6))))))
nested_list = [1, [2, [3, [4, [5, [6, []]]]]]]
@test (pformat(pprint, nested_tuple) == repr(nested_tuple))
@test (pformat(pprint, nested_dict) == repr(nested_dict))
@test (pformat(pprint, nested_list) == repr(nested_list))
lv1_tuple = "(1, (...))"
lv1_dict = "{1: {...}}"
lv1_list = "[1, [...]]"
@test (pformat(pprint, nested_tuple, 1) == lv1_tuple)
@test (pformat(pprint, nested_dict, 1) == lv1_dict)
@test (pformat(pprint, nested_list, 1) == lv1_list)
end

function test_sort_unorderable_values(self::QueryTestCase)
n = 20
keys = [Unorderable() for i in 0:n - 1]
shuffle(random, keys)
skeys = sorted(keys, id)
clean = (s) -> replace(replace(s, " ", ""), "\n", "")
@test (clean(pformat(pprint, set(keys))) == ("{" + join(map(repr, skeys), ",")) * "}")
@test (clean(pformat(pprint, frozenset(keys))) == ("frozenset({" + join(map(repr, skeys), ",")) * "})")
@test (clean(pformat(pprint, fromkeys(dict, keys))) == ("{" + join(("%r:None" % k for k in skeys), ",")) * "}")
@test (pformat(pprint, Dict(Unorderable => 0, 1 => 0)) == ("{1: 0, " + repr(Unorderable)) * ": 0}")
keys = [(1,), (nothing,)]
@test (pformat(pprint, fromkeys(dict, keys, 0)) == "{%r: 0, %r: 0}" % tuple(sorted(keys, id)))
end

function test_sort_orderable_and_unorderable_values(self::QueryTestCase)
a = Unorderable()
b = Orderable(hash(a))
assertLess(self, a, b)
assertLess(self, string(type_(b)), string(type_(a)))
@test (sorted([b, a]) == [a, b])
@test (sorted([a, b]) == [a, b])
@test (pformat(pprint, set([b, a]), 1) == "{%r,\n %r}" % (a, b))
@test (pformat(pprint, set([a, b]), 1) == "{%r,\n %r}" % (a, b))
@test (pformat(pprint, fromkeys(dict, [b, a]), 1) == "{%r: None,\n %r: None}" % (a, b))
@test (pformat(pprint, fromkeys(dict, [a, b]), 1) == "{%r: None,\n %r: None}" % (a, b))
end

function test_str_wrap(self::QueryTestCase)
fox = "the quick brown fox jumped over a lazy dog"
@test (pformat(pprint, fox, 19) == "(\'the quick brown \'\n \'fox jumped over \'\n \'a lazy dog\')")
@test (pformat(pprint, Dict("a" => 1, "b" => fox, "c" => 2), 25) == "{\'a\': 1,\n \'b\': \'the quick brown \'\n      \'fox jumped over \'\n      \'a lazy dog\',\n \'c\': 2}")
special = "Portons dix bons \"whiskys\"\nà l\'avocat goujat\t qui fumait au zoo"
@test (pformat(pprint, special, 68) == repr(special))
@test (pformat(pprint, special, 31) == "(\'Portons dix bons \"whiskys\"\\n\'\n \"à l\'avocat goujat\\t qui \"\n \'fumait au zoo\')")
@test (pformat(pprint, special, 20) == "(\'Portons dix bons \'\n \'\"whiskys\"\\n\'\n \"à l\'avocat \"\n \'goujat\\t qui \'\n \'fumait au zoo\')")
@test (pformat(pprint, [[[[[special]]]]], 35) == "[[[[[\'Portons dix bons \"whiskys\"\\n\'\n     \"à l\'avocat goujat\\t qui \"\n     \'fumait au zoo\']]]]]")
@test (pformat(pprint, [[[[[special]]]]], 25) == "[[[[[\'Portons dix bons \'\n     \'\"whiskys\"\\n\'\n     \"à l\'avocat \"\n     \'goujat\\t qui \'\n     \'fumait au zoo\']]]]]")
@test (pformat(pprint, [[[[[special]]]]], 23) == "[[[[[\'Portons dix \'\n     \'bons \"whiskys\"\\n\'\n     \"à l\'avocat \"\n     \'goujat\\t qui \'\n     \'fumait au \'\n     \'zoo\']]]]]")
unwrappable = repeat("x",100)
@test (pformat(pprint, unwrappable, 80) == repr(unwrappable))
@test (pformat(pprint, "") == "\'\'")
special *= 10
for width in 3:39
formatted = pformat(pprint, special, width)
@test (eval(formatted) == special)
formatted = pformat(pprint, repeat([special],2), width)
@test (eval(formatted) == repeat([special],2))
end
end

function test_compact(self::QueryTestCase)
o = [collect(0:i*i - 1) for i in 0:4] + [collect(0:i - 1) for i in 0:5]
expected = "[[], [0], [0, 1, 2, 3],\n [0, 1, 2, 3, 4, 5, 6, 7, 8],\n [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,\n  14, 15],\n [], [0], [0, 1], [0, 1, 2], [0, 1, 2, 3],\n [0, 1, 2, 3, 4]]"
@test (pformat(pprint, o, 47, true) == expected)
end

function test_compact_width(self::QueryTestCase)
levels = 20
number = 10
o = repeat([0],number)
for i in 0:levels - 2
o = [o]
end
for w in levels*2:(levels + 3*number) - 2
lines = splitlines(pformat(pprint, o, w, true))
maxwidth = max(map(len, lines))
assertLessEqual(self, maxwidth, w)
assertGreater(self, maxwidth, w - 3)
end
end

function test_bytes_wrap(self::QueryTestCase)
@test (pformat(pprint, b"", 1) == "b\'\'")
@test (pformat(pprint, b"abcd", 1) == "b\'abcd\'")
letters = b"abcdefghijklmnopqrstuvwxyz"
@test (pformat(pprint, letters, 29) == repr(letters))
@test (pformat(pprint, letters, 19) == "(b\'abcdefghijkl\'\n b\'mnopqrstuvwxyz\')")
@test (pformat(pprint, letters, 18) == "(b\'abcdefghijkl\'\n b\'mnopqrstuvwx\'\n b\'yz\')")
@test (pformat(pprint, letters, 16) == "(b\'abcdefghijkl\'\n b\'mnopqrstuvwx\'\n b\'yz\')")
special = bytes(0:15)
@test (pformat(pprint, special, 61) == repr(special))
@test (pformat(pprint, special, 48) == "(b\'\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\'\n b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, special, 32) == "(b\'\\x00\\x01\\x02\\x03\'\n b\'\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\'\n b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, special, 1) == "(b\'\\x00\\x01\\x02\\x03\'\n b\'\\x04\\x05\\x06\\x07\'\n b\'\\x08\\t\\n\\x0b\'\n b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, Dict("a" => 1, "b" => letters, "c" => 2), 21) == "{\'a\': 1,\n \'b\': b\'abcdefghijkl\'\n      b\'mnopqrstuvwx\'\n      b\'yz\',\n \'c\': 2}")
@test (pformat(pprint, Dict("a" => 1, "b" => letters, "c" => 2), 20) == "{\'a\': 1,\n \'b\': b\'abcdefgh\'\n      b\'ijklmnop\'\n      b\'qrstuvwxyz\',\n \'c\': 2}")
@test (pformat(pprint, [[[[[[letters]]]]]], 25) == "[[[[[[b\'abcdefghijklmnop\'\n      b\'qrstuvwxyz\']]]]]]")
@test (pformat(pprint, [[[[[[special]]]]]], 41) == "[[[[[[b\'\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\'\n      b\'\\x08\\t\\n\\x0b\\x0c\\r\\x0e\\x0f\']]]]]]")
for width in 1:63
formatted = pformat(pprint, special, width)
@test (eval(formatted) == special)
formatted = pformat(pprint, repeat([special],2), width)
@test (eval(formatted) == repeat([special],2))
end
end

function test_bytearray_wrap(self::QueryTestCase)
@test (pformat(pprint, Vector{UInt8}(), 1) == "bytearray(b\'\')")
letters = Vector{UInt8}(b"abcdefghijklmnopqrstuvwxyz")
@test (pformat(pprint, letters, 40) == repr(letters))
@test (pformat(pprint, letters, 28) == "bytearray(b\'abcdefghijkl\'\n          b\'mnopqrstuvwxyz\')")
@test (pformat(pprint, letters, 27) == "bytearray(b\'abcdefghijkl\'\n          b\'mnopqrstuvwx\'\n          b\'yz\')")
@test (pformat(pprint, letters, 25) == "bytearray(b\'abcdefghijkl\'\n          b\'mnopqrstuvwx\'\n          b\'yz\')")
special = Vector{UInt8}(0:15)
@test (pformat(pprint, special, 72) == repr(special))
@test (pformat(pprint, special, 57) == "bytearray(b\'\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\'\n          b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, special, 41) == "bytearray(b\'\\x00\\x01\\x02\\x03\'\n          b\'\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\'\n          b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, special, 1) == "bytearray(b\'\\x00\\x01\\x02\\x03\'\n          b\'\\x04\\x05\\x06\\x07\'\n          b\'\\x08\\t\\n\\x0b\'\n          b\'\\x0c\\r\\x0e\\x0f\')")
@test (pformat(pprint, Dict("a" => 1, "b" => letters, "c" => 2), 31) == "{\'a\': 1,\n \'b\': bytearray(b\'abcdefghijkl\'\n                b\'mnopqrstuvwx\'\n                b\'yz\'),\n \'c\': 2}")
@test (pformat(pprint, [[[[[letters]]]]], 37) == "[[[[[bytearray(b\'abcdefghijklmnop\'\n               b\'qrstuvwxyz\')]]]]]")
@test (pformat(pprint, [[[[[special]]]]], 50) == "[[[[[bytearray(b\'\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\'\n               b\'\\x08\\t\\n\\x0b\\x0c\\r\\x0e\\x0f\')]]]]]")
end

function test_default_dict(self::QueryTestCase)
d = defaultdict(collections, int)
@test (pformat(pprint, d, 1) == "defaultdict(<class \'int\'>, {})")
words = split("the quick brown fox jumped over a lazy dog")
d = defaultdict(collections, int, zip(words, count(itertools)))
@test (pformat(pprint, d) == "defaultdict(<class \'int\'>,\n            {\'a\': 6,\n             \'brown\': 2,\n             \'dog\': 8,\n             \'fox\': 3,\n             \'jumped\': 4,\n             \'lazy\': 7,\n             \'over\': 5,\n             \'quick\': 1,\n             \'the\': 0})")
end

function test_counter(self::QueryTestCase)
d = Counter(collections)
@test (pformat(pprint, d, 1) == "Counter()")
d = Counter(collections, "senselessness")
@test (pformat(pprint, d, 40) == "Counter({\'s\': 6,\n         \'e\': 4,\n         \'n\': 2,\n         \'l\': 1})")
end

function test_chainmap(self::QueryTestCase)
d = ChainMap(collections)
@test (pformat(pprint, d, 1) == "ChainMap({})")
words = split("the quick brown fox jumped over a lazy dog")
items = collect(zip(words, count(itertools)))
d = ChainMap(collections, dict(items))
@test (pformat(pprint, d) == "ChainMap({\'a\': 6,\n          \'brown\': 2,\n          \'dog\': 8,\n          \'fox\': 3,\n          \'jumped\': 4,\n          \'lazy\': 7,\n          \'over\': 5,\n          \'quick\': 1,\n          \'the\': 0})")
d = ChainMap(collections, dict(items), OrderedDict(collections, items))
@test (pformat(pprint, d) == "ChainMap({\'a\': 6,\n          \'brown\': 2,\n          \'dog\': 8,\n          \'fox\': 3,\n          \'jumped\': 4,\n          \'lazy\': 7,\n          \'over\': 5,\n          \'quick\': 1,\n          \'the\': 0},\n         OrderedDict([(\'the\', 0),\n                      (\'quick\', 1),\n                      (\'brown\', 2),\n                      (\'fox\', 3),\n                      (\'jumped\', 4),\n                      (\'over\', 5),\n                      (\'a\', 6),\n                      (\'lazy\', 7),\n                      (\'dog\', 8)]))")
end

function test_deque(self::QueryTestCase)
d = deque(collections)
@test (pformat(pprint, d, 1) == "deque([])")
d = deque(collections, 7)
@test (pformat(pprint, d, 1) == "deque([], maxlen=7)")
words = split("the quick brown fox jumped over a lazy dog")
d = deque(collections, zip(words, count(itertools)))
@test (pformat(pprint, d) == "deque([(\'the\', 0),\n       (\'quick\', 1),\n       (\'brown\', 2),\n       (\'fox\', 3),\n       (\'jumped\', 4),\n       (\'over\', 5),\n       (\'a\', 6),\n       (\'lazy\', 7),\n       (\'dog\', 8)])")
d = deque(collections, zip(words, count(itertools)), 7)
@test (pformat(pprint, d) == "deque([(\'brown\', 2),\n       (\'fox\', 3),\n       (\'jumped\', 4),\n       (\'over\', 5),\n       (\'a\', 6),\n       (\'lazy\', 7),\n       (\'dog\', 8)],\n      maxlen=7)")
end

function test_user_dict(self::QueryTestCase)
d = UserDict(collections)
@test (pformat(pprint, d, 1) == "{}")
words = split("the quick brown fox jumped over a lazy dog")
d = UserDict(collections, zip(words, count(itertools)))
@test (pformat(pprint, d) == "{\'a\': 6,\n \'brown\': 2,\n \'dog\': 8,\n \'fox\': 3,\n \'jumped\': 4,\n \'lazy\': 7,\n \'over\': 5,\n \'quick\': 1,\n \'the\': 0}")
end

function test_user_list(self::QueryTestCase)
d = UserList(collections)
@test (pformat(pprint, d, 1) == "[]")
words = split("the quick brown fox jumped over a lazy dog")
d = UserList(collections, zip(words, count(itertools)))
@test (pformat(pprint, d) == "[(\'the\', 0),\n (\'quick\', 1),\n (\'brown\', 2),\n (\'fox\', 3),\n (\'jumped\', 4),\n (\'over\', 5),\n (\'a\', 6),\n (\'lazy\', 7),\n (\'dog\', 8)]")
end

function test_user_string(self::QueryTestCase)
d = UserString(collections, "")
@test (pformat(pprint, d, 1) == "\'\'")
d = UserString(collections, "the quick brown fox jumped over a lazy dog")
@test (pformat(pprint, d, 20) == "(\'the quick brown \'\n \'fox jumped over \'\n \'a lazy dog\')")
@test (pformat(pprint, Dict(1 => d), 20) == "{1: \'the quick \'\n    \'brown fox \'\n    \'jumped over a \'\n    \'lazy dog\'}")
end

mutable struct DottedPrettyPrinter <: AbstractDottedPrettyPrinter

end
function format(self::DottedPrettyPrinter, object, context, maxlevels, level)::Tuple
if isa(object, str)
if " " ∈ object
return (repr(object), 1, 0)
else
return (object, 0, 0)
end
else
return pprint.PrettyPrinter
end
end

function main()
query_test_case = QueryTestCase()
setUp(query_test_case)
test_init(query_test_case)
test_basic(query_test_case)
test_knotted(query_test_case)
test_unreadable(query_test_case)
test_same_as_repr(query_test_case)
test_container_repr_override_called(query_test_case)
test_basic_line_wrap(query_test_case)
test_nested_indentations(query_test_case)
test_width(query_test_case)
test_integer(query_test_case)
test_sorted_dict(query_test_case)
test_sort_dict(query_test_case)
test_ordered_dict(query_test_case)
test_mapping_proxy(query_test_case)
test_empty_simple_namespace(query_test_case)
test_small_simple_namespace(query_test_case)
test_simple_namespace(query_test_case)
test_simple_namespace_subclass(query_test_case)
test_empty_dataclass(query_test_case)
test_small_dataclass(query_test_case)
test_larger_dataclass(query_test_case)
test_dataclass_with_repr(query_test_case)
test_dataclass_no_repr(query_test_case)
test_recursive_dataclass(query_test_case)
test_cyclic_dataclass(query_test_case)
test_subclassing(query_test_case)
test_set_reprs(query_test_case)
test_set_of_sets_reprs(query_test_case)
test_depth(query_test_case)
test_sort_unorderable_values(query_test_case)
test_sort_orderable_and_unorderable_values(query_test_case)
test_str_wrap(query_test_case)
test_compact(query_test_case)
test_compact_width(query_test_case)
test_bytes_wrap(query_test_case)
test_bytearray_wrap(query_test_case)
test_default_dict(query_test_case)
test_counter(query_test_case)
test_chainmap(query_test_case)
test_deque(query_test_case)
test_user_dict(query_test_case)
test_user_list(query_test_case)
test_user_string(query_test_case)
end

main()