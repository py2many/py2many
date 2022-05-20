using PyCall
pythoncom = pyimport("pythoncom")

using win32com_.client.gencache: EnsureDispatch
using win32com_.client: Dispatch
import win32com_.server.util
import win32com_.test.util

abstract type Abstract_BaseTestCase <: Abstractwin32com_.test.util.TestCase end
abstract type AbstractVBTestCase <: Abstract_BaseTestCase end
abstract type AbstractSomeObject end
abstract type AbstractWrappedPythonCOMServerTestCase <: Abstract_BaseTestCase end
mutable struct _BaseTestCase <: Abstract_BaseTestCase
    expected_data
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
    object
    expected_data::Vector{Union{String, Int64}}
    iter_factory
end
function setUp(self::VBTestCase)
    function factory()::Tuple
        ob = self.object.EnumerableCollectionProperty
        for i in self.expected_data
            Add(ob, i)
        end
        invkind = pythoncom.DISPATCH_METHOD | pythoncom.DISPATCH_PROPERTYGET
        iter = InvokeTypes(ob._oleobj_, pythoncom.DISPID_NEWENUM, 0, invkind, (13, 10), ())
        return (ob, QueryInterface(iter, pythoncom.IID_IEnumVARIANT))
    end

    self.object = EnsureDispatch("PyCOMVBTest.Tester")
    self.expected_data = [1, "Two", "3"]
    self.iter_factory = factory
end

function tearDown(self::VBTestCase)
    self.object = nothing
end

mutable struct SomeObject <: AbstractSomeObject
    data
    _public_methods_::Vector{String}

    SomeObject(data, _public_methods_::Vector{String} = ["GetCollection"]) =
        new(data, _public_methods_)
end
function GetCollection(self::SomeObject)
    return NewCollection(win32com_.server.util, self.data)
end

mutable struct WrappedPythonCOMServerTestCase <: AbstractWrappedPythonCOMServerTestCase
    expected_data::Vector{Union{String, Int64}}
    object
    iter_factory
end
function setUp(self::WrappedPythonCOMServerTestCase)
    function factory()::Tuple
        ob = GetCollection(self.object)
        flags = pythoncom.DISPATCH_METHOD | pythoncom.DISPATCH_PROPERTYGET
        enum = Invoke(ob._oleobj_, pythoncom.DISPID_NEWENUM, 0, flags, 1)
        return (ob, QueryInterface(enum, pythoncom.IID_IEnumVARIANT))
    end

    self.expected_data = [1, "Two", 3]
    sv = wrap(win32com_.server.util, SomeObject(self.expected_data))
    self.object = Dispatch(sv)
    self.iter_factory = factory
end

function tearDown(self::WrappedPythonCOMServerTestCase)
    self.object = nothing
end

function suite()
    suite = TestSuite(unittest)
    for item in collect(values(globals()))
        if type_(item) == type_(unittest.TestCase) &&
           item <: unittest.TestCase &&
           item != _BaseTestCase
            addTest(suite, makeSuite(unittest, item))
        end
    end
    return suite
end

if abspath(PROGRAM_FILE) == @__FILE__
end
