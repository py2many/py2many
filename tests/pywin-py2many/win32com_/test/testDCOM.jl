using Printf
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")
usage = "testDCOM.py - Simple DCOM test\nUsage: testDCOM.py serverName\n\nAttempts to start the Python.Interpreter object on the named machine,\nand checks that the object is indeed running remotely.\n\nRequires the named server be configured to run DCOM (using dcomcnfg.exe),\nand the Python.Interpreter object installed and registered on that machine.\n\nThe Python.Interpreter object must be installed on the local machine,\nbut no special DCOM configuration should be necessary.\n"
import win32com_.client
import string
function test(serverName)
    if lower(string, serverName) == lower(string, GetComputerName(win32api))
        println("You must specify a remote server name, not the local machine!")
        return
    end
    clsctx = pythoncom.CLSCTX_SERVER & ~(pythoncom.CLSCTX_INPROC_SERVER)
    ob = DispatchEx(win32com_.client, "Python.Interpreter", serverName, clsctx)
    Exec(ob, "import win32api")
    actualName = Eval(ob, "win32api.GetComputerName()")
    if lower(string, serverName) != lower(string, actualName)
        @printf(
            "Error: The object created on server \'%s\' reported its name as \'%s\'\n",
            serverName,
            actualName
        )
    else
        @printf("Object created and tested OK on server \'%s\'\n", serverName)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    if length(append!([PROGRAM_FILE], ARGS)) == 2
        test(append!([PROGRAM_FILE], ARGS)[2])
    else
        println(usage)
    end
end
