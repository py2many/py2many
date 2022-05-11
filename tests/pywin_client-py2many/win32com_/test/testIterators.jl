module testIterators
using PyCall
pythoncom = pyimport("pythoncom")


using win32com.client.gencache: EnsureDispatch
using win32com.client: Dispatch
import win32com.server.util
import win32com.test.util

abstract type Abstract_BaseTestCase <: Abstractwin32com.test.util.TestCase end
abstract type AbstractVBTestCase <: Abstract_BaseTestCase end
abstract type AbstractSomeObject end
abstract type AbstractWrappedPythonCOMServerTestCase <: Abstract_BaseTestCase end
mutable struct _BaseTestCase <: Abstract_BaseTestCase
expected_data::Any
end
function test_enumvariant_vb(self::_BaseTestCase)
ob, iter = iter_factory(self)
got = []
for v in iter
push!(got, v)
end
assertEqual(self, got, self.expected_data)
end

function test_yield(self::_BaseTestCase)
ob, i = iter_factory(self)
got = []
for v in (x for x in i)
push!(got, v)
end
assertEqual(self, got, self.expected_data)
end

function _do_test_nonenum(self::_BaseTestCase, object)
try
for i in object
#= pass =#
end
fail(self, "Could iterate over a non-iterable object")
catch exn
if exn isa TypeError
#= pass =#
end
end
assertRaises(self, TypeError, iter, object)
assertRaises(self, AttributeError, getattr, object, "next")
end

function test_nonenum_wrapper(self::_BaseTestCase)
ob = self.object._oleobj_
try
for i in ob
#= pass =#
end
fail(self, "Could iterate over a non-iterable object")
catch exn
if exn isa TypeError
#= pass =#
end
end
assertRaises(self, TypeError, iter, ob)
assertRaises(self, AttributeError, getattr, ob, "next")
ob = self.object
try
for i in ob
#= pass =#
end
fail(self, "Could iterate over a non-iterable object")
catch exn
if exn isa TypeError
#= pass =#
end
end
try
next((x for x in ob))
fail(self, "Expected a TypeError fetching this iterator")
catch exn
if exn isa TypeError
#= pass =#
end
end
assertRaises(self, AttributeError, getattr, ob, "next")
end

mutable struct VBTestCase <: AbstractVBTestCase
expected_data::Any
object::Any
iter_factory::Any
end
function setUp(self::VBTestCase)
function factory()::Tuple
ob = self.object.EnumerableCollectionProperty
for i in self.expected_data
Add(ob, i)
end
invkind = DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom)
iter = InvokeTypes(ob._oleobj_, DISPID_NEWENUM(pythoncom), 0, invkind, (13, 10), ())
return (ob, QueryInterface(iter, IID_IEnumVARIANT(pythoncom)))
end

self.object = EnsureDispatch("PyCOMVBTest.Tester")
self.expected_data = [1, "Two", "3"]
self.iter_factory = factory
end

function tearDown(self::VBTestCase)
self.object = nothing
end

mutable struct SomeObject <: AbstractSomeObject
data::Any
_public_methods_::Vector{String}

                    SomeObject(data::Any, _public_methods_::Vector{String} = ["GetCollection"]) =
                        new(data, _public_methods_)
end
function GetCollection(self::SomeObject)
return NewCollection(win32com.server.util, self.data)
end

mutable struct WrappedPythonCOMServerTestCase <: AbstractWrappedPythonCOMServerTestCase
expected_data::Any
object::Any
iter_factory::Any
end
function setUp(self::WrappedPythonCOMServerTestCase)
function factory()::Tuple
ob = GetCollection(self.object)
flags = DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom)
enum = Invoke(ob._oleobj_, DISPID_NEWENUM(pythoncom), 0, flags, 1)
return (ob, QueryInterface(enum, IID_IEnumVARIANT(pythoncom)))
end

self.expected_data = [1, "Two", 3]
sv = wrap(win32com.server.util, SomeObject(self.expected_data))
self.object = Dispatch(sv)
self.iter_factory = factory
end

function tearDown(self::WrappedPythonCOMServerTestCase)
self.object = nothing
end

function suite()
suite = TestSuite(unittest)
for item in collect(values(globals()))
if type_(item) == type_(TestCase(unittest)) && item <: TestCase(unittest) && item != _BaseTestCase
addTest(suite, makeSuite(unittest, item))
end
end
return suite
end

function main()

end

main()
end