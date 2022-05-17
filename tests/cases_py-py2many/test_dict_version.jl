#= 
Test implementation of the PEP 509: dictionary versioning.
 =#
using Test


abstract type AbstractDictVersionTests end
abstract type AbstractAlwaysEqual end
abstract type AbstractDict <: Abstractdict end
abstract type AbstractDictSubtypeVersionTests <: AbstractDictVersionTests end
_testcapi = import_module(import_helper, "_testcapi")
mutable struct DictVersionTests <: AbstractDictVersionTests
assertRaises
dict
seen_versions
type2test

                    DictVersionTests(assertRaises, dict, seen_versions, type2test = dict) =
                        new(assertRaises, dict, seen_versions, type2test)
end
function setUp(self::DictVersionTests)
self.seen_versions = set()
self.dict = nothing
end

function check_version_unique(self::DictVersionTests, mydict)
version = dict_get_version(_testcapi, mydict)
assertNotIn(self, version, self.seen_versions)
add(self.seen_versions, version)
end

function check_version_changed(self::DictVersionTests, mydict, method)
result = method(args..., kw)
check_version_unique(self, mydict)
return result
end

function check_version_dont_change(self::DictVersionTests, mydict, method)
version1 = dict_get_version(_testcapi, mydict)
add(self.seen_versions, version1)
result = method(args..., kw)
version2 = dict_get_version(_testcapi, mydict)
@test (version2 == version1)
return result
end

function new_dict(self::DictVersionTests)
d = type2test(self, args..., kw)
check_version_unique(self, d)
return d
end

function test_constructor(self::DictVersionTests)
empty1 = new_dict(self)
empty2 = new_dict(self)
empty3 = new_dict(self)
nonempty1 = new_dict(self)
nonempty2 = new_dict(self)
end

function test_copy(self::DictVersionTests)
d = new_dict(self)
d2 = check_version_dont_change(self, d, d.copy)
check_version_unique(self, d2)
end

function test_setitem(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.__setitem__)
check_version_changed(self, d, d.__setitem__)
check_version_changed(self, d, d.__setitem__)
check_version_changed(self, d, d.__setitem__)
end

function test_setitem_same_value(self::DictVersionTests)
value = object()
d = new_dict(self)
check_version_changed(self, d, d.__setitem__)
check_version_dont_change(self, d, d.__setitem__)
check_version_dont_change(self, d, d.update)
d2 = new_dict(self)
check_version_dont_change(self, d, d.update)
end

function test_setitem_equal(self::AlwaysEqual)
mutable struct AlwaysEqual <: AbstractAlwaysEqual

end
function __eq__(self::AlwaysEqual, other)::Bool
return true
end

value1 = AlwaysEqual()
value2 = AlwaysEqual()
assertTrue(self, value1 == value2)
assertFalse(self, value1 != value2)
assertIsNot(self, value1, value2)
d = new_dict(self)
check_version_changed(self, d, d.__setitem__)
assertIs(self, d["key"], value1)
check_version_changed(self, d, d.__setitem__)
assertIs(self, d["key"], value2)
check_version_changed(self, d, d.update)
assertIs(self, d["key"], value1)
d2 = new_dict(self)
check_version_changed(self, d, d.update)
assertIs(self, d["key"], value2)
end

function test_setdefault(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.setdefault)
check_version_dont_change(self, d, d.setdefault)
end

function test_delitem(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.__delitem__)
check_version_dont_change(self, d, self.assertRaises)
end

function test_pop(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.pop)
check_version_dont_change(self, d, self.assertRaises)
end

function test_popitem(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.popitem)
check_version_dont_change(self, d, self.assertRaises)
end

function test_update(self::DictVersionTests)
d = new_dict(self)
check_version_dont_change(self, d, d.update)
check_version_changed(self, d, d.update)
d2 = new_dict(self)
check_version_changed(self, d, d.update)
end

function test_clear(self::DictVersionTests)
d = new_dict(self)
check_version_changed(self, d, d.clear)
check_version_dont_change(self, d, d.clear)
end

mutable struct Dict <: AbstractDict

end

mutable struct DictSubtypeVersionTests <: AbstractDictSubtypeVersionTests
type2test::Dict{Any}

                    DictSubtypeVersionTests(type2test::Dict{Any} = Dict) =
                        new(type2test)
end

function main()
dict_version_tests = DictVersionTests()
setUp(dict_version_tests)
check_version_unique(dict_version_tests)
check_version_changed(dict_version_tests)
check_version_dont_change(dict_version_tests)
new_dict(dict_version_tests)
test_constructor(dict_version_tests)
test_copy(dict_version_tests)
test_setitem(dict_version_tests)
test_setitem_same_value(dict_version_tests)
test_setitem_equal(dict_version_tests)
test_setdefault(dict_version_tests)
test_delitem(dict_version_tests)
test_pop(dict_version_tests)
test_popitem(dict_version_tests)
test_update(dict_version_tests)
test_clear(dict_version_tests)
end

main()