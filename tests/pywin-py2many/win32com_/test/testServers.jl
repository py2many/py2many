using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.demos.connect
import RegisterPythonServer
using win32com_.servers: interp
include("win32com_/client/dynamic.jl")
import winerror
include("win32com_/test/util.jl")

abstract type AbstractInterpCase <: Abstractwin32com_.test.util.TestCase end
abstract type AbstractConnectionsTestCase <: Abstractwin32com_.test.util.TestCase end
function TestConnections()
test(win32com_.demos.connect)
end

mutable struct InterpCase <: AbstractInterpCase

end
function setUp(self::InterpCase)
RegisterPythonServer(interp.__file__, "Python.Interpreter")
end

function _testInterp(self::InterpCase, interp)
assertEqual(self, Eval(interp, "1+1"), 2)
assertRaisesCOM_HRESULT(win32com_.test.util, self, winerror.DISP_E_TYPEMISMATCH, interp.Eval, 2)
end

function testInproc(self::InterpCase)
interp = Dispatch(win32com_.client.dynamic, "Python.Interpreter", pythoncom.CLSCTX_INPROC)
_testInterp(self, interp)
end

function testLocalServer(self::InterpCase)
interp = Dispatch(win32com_.client.dynamic, "Python.Interpreter", pythoncom.CLSCTX_LOCAL_SERVER)
_testInterp(self, interp)
end

function testAny(self::InterpCase)
interp = Dispatch(win32com_.client.dynamic, "Python.Interpreter")
_testInterp(self, interp)
end

mutable struct ConnectionsTestCase <: AbstractConnectionsTestCase

end
function testConnections(self::ConnectionsTestCase)
TestConnections()
end

function main()

end

main()