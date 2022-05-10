module policySemantics
using PyCall
pythoncom = pyimport("pythoncom")
import win32com.server.dispatcher
import win32com.server.util
import win32com.client

import winerror
import win32com.test.util

abstract type AbstractError <: AbstractException end
abstract type AbstractPythonSemanticClass end
abstract type AbstractTester <: Abstractwin32com.test.util.TestCase end
mutable struct Error <: AbstractError

end

mutable struct PythonSemanticClass <: AbstractPythonSemanticClass
_dispid_to_func_::Dict{Int64, String}
_public_methods_::Vector{String}
list::Vector

                    PythonSemanticClass(_dispid_to_func_::Dict{Int64, String} = Dict(10 => "Add", 11 => "Remove"), _public_methods_::Vector{String} = ["In"], list::Vector = []) =
                        new(_dispid_to_func_, _public_methods_, list)
end
function _NewEnum(self::PythonSemanticClass)
return NewEnum(win32com.server.util, self.list)
end

function _value_(self::PythonSemanticClass)::PythonSemanticClass
return self.list
end

function _Evaluate(self::PythonSemanticClass)
return sum(self.list)
end

function In(self::PythonSemanticClass, value)::Bool
return value in self.list
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
@assert(GetDispID(ob, "_NewEnum", 0) == DISPID_NEWENUM(pythoncom))
dispids = []
dispid = -1
while true
try
dispid = GetNextDispID(ob, 0, dispid)
append(dispids, dispid)
catch exn
 let xxx_todo_changeme = exn
if xxx_todo_changeme isa com_error(pythoncom)
hr, desc, exc, arg = args(xxx_todo_changeme)
@assert(hr == winerror.S_FALSE)
break;
end
end
end
end
sort(dispids)
if dispids != [DISPID_EVALUATE(pythoncom), DISPID_NEWENUM(pythoncom), 10, 11, 1000]
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
dispob = _oleobj_(ob)
rc = Invoke(dispob, DISPID_EVALUATE(pythoncom), 0, DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom), 1)
if rc != 6
throw(Error("Evaluate returned %d" % rc))
end
end

mutable struct Tester <: AbstractTester
ob::Any
end
function setUp(self::Tester)
debug = 0
if debug != 0
dispatcher = win32com.server.dispatcher.DefaultDebugDispatcher
else
dispatcher = nothing
end
disp = wrap(win32com.server.util, PythonSemanticClass(), dispatcher)
self.ob = Dispatch(win32com.client, disp)
end

function tearDown(self::Tester)
self.ob = nothing
end

function testSemantics(self::Tester)
SemanticTest(self.ob)
end

function testIDispatchEx(self::Tester)
dispexob = QueryInterface(self.ob._oleobj_, IID_IDispatchEx(pythoncom))
DispExTest(dispexob)
end

function main()

end

main()
end