using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.server.dispatcher
import win32com_.server.util
import win32com_.client

import winerror
import win32com_.test.util

abstract type AbstractError <: AbstractException end
abstract type AbstractPythonSemanticClass end
abstract type AbstractTester <: Abstractwin32com_.test.util.TestCase end
mutable struct Error <: AbstractError
end

mutable struct PythonSemanticClass <: AbstractPythonSemanticClass
    list::Vector
    _dispid_to_func_::Dict{Int64, String}
    _public_methods_::Vector{String}

    PythonSemanticClass(
        list::Vector,
        _dispid_to_func_::Dict{Int64, String} = Dict(10 => "Add", 11 => "Remove"),
        _public_methods_::Vector{String} = ["In"],
    ) = new(list, _dispid_to_func_, _public_methods_)
end
function _NewEnum(self::PythonSemanticClass)
    return NewEnum(win32com_.server.util, self.list)
end

function _value_(self::PythonSemanticClass)::Vector
    return self.list
end

function _Evaluate(self::PythonSemanticClass)
    return sum(self.list)
end

function In(self::PythonSemanticClass, value)::Bool
    return value ∈ self.list
end

function Add(self::PythonSemanticClass, value)
    append(self.list, value)
end

function Remove(self::PythonSemanticClass, value)
    remove(self.list, value)
end

function DispExTest(ob)
    if !(__debug__)
        println("WARNING: Tests dressed up as assertions are being skipped!")
    end
    @assert(GetDispID(ob, "Add", 0) == 10)
    @assert(GetDispID(ob, "Remove", 0) == 11)
    @assert(GetDispID(ob, "In", 0) == 1000)
    @assert(GetDispID(ob, "_NewEnum", 0) == pythoncom.DISPID_NEWENUM)
    dispids = []
    dispid = -1
    while true
        try
            dispid = GetNextDispID(ob, 0, dispid)
            push!(dispids, dispid)
        catch exn
            let xxx_todo_changeme = exn
                if xxx_todo_changeme isa pythoncom.com_error
                    hr, desc, exc, arg = xxx_todo_changeme.args
                    @assert(hr == winerror.S_FALSE)
                    break
                end
            end
        end
    end
    sort(dispids)
    if dispids != [pythoncom.DISPID_EVALUATE, pythoncom.DISPID_NEWENUM, 10, 11, 1000]
        throw(Error("Got back the wrong dispids: %s" % dispids))
    end
end

function SemanticTest(ob)
    Add(ob, 1)
    Add(ob, 2)
    Add(ob, 3)
    if ob() != (1, 2, 3)
        throw(Error("Bad result - got %s" % repr(ob())))
    end
    dispob = ob._oleobj_
    rc = Invoke(
        dispob,
        pythoncom.DISPID_EVALUATE,
        0,
        pythoncom.DISPATCH_METHOD | pythoncom.DISPATCH_PROPERTYGET,
        1,
    )
    if rc != 6
        throw(Error("Evaluate returned %d" % rc))
    end
end

mutable struct Tester <: AbstractTester
    ob
end
function setUp(self::Tester)
    debug = 0
    if debug != 0
        dispatcher = win32com_.server.dispatcher.DefaultDebugDispatcher
    else
        dispatcher = nothing
    end
    disp = wrap(win32com_.server.util, PythonSemanticClass(), dispatcher)
    self.ob = Dispatch(win32com_.client, disp)
end

function tearDown(self::Tester)
    self.ob = nothing
end

function testSemantics(self::Tester)
    SemanticTest(self.ob)
end

function testIDispatchEx(self::Tester)
    dispexob = QueryInterface(self.ob._oleobj_, pythoncom.IID_IDispatchEx)
    DispExTest(dispexob)
end

if abspath(PROGRAM_FILE) == @__FILE__
end
