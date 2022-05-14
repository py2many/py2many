module testServers
using PyCall
pythoncom = pyimport("pythoncom")
import win32com.demos.connect
using win32com.test.util: RegisterPythonServer
using win32com.servers: interp
import win32com.client.dynamic
import winerror
import win32com.test.util

abstract type AbstractInterpCase <: Abstractwin32com.test.util.TestCase end
abstract type AbstractConnectionsTestCase <: Abstractwin32com.test.util.TestCase end
function TestConnections()
    test(win32com.demos.connect)
end

mutable struct InterpCase <: AbstractInterpCase
end
function setUp(self::InterpCase)
    RegisterPythonServer(interp.__file__, "Python.Interpreter")
end

function _testInterp(self::InterpCase, interp)
    assertEqual(self, Eval(interp, "1+1"), 2)
    assertRaisesCOM_HRESULT(
        win32com.test.util,
        self,
        winerror.DISP_E_TYPEMISMATCH,
        interp.Eval,
        2,
    )
end

function testInproc(self::InterpCase)
    interp = Dispatch(
        win32com.client.dynamic,
        "Python.Interpreter",
        clsctx = pythoncom.CLSCTX_INPROC,
    )
    _testInterp(self, interp)
end

function testLocalServer(self::InterpCase)
    interp = Dispatch(
        win32com.client.dynamic,
        "Python.Interpreter",
        clsctx = pythoncom.CLSCTX_LOCAL_SERVER,
    )
    _testInterp(self, interp)
end

function testAny(self::InterpCase)
    interp = Dispatch(win32com.client.dynamic, "Python.Interpreter")
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
end
