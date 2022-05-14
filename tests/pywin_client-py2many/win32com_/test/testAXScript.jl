module testAXScript
using PyCall
win32api = pyimport("win32api")
using win32com.test.util: RegisterPythonServer

import win32com.axscript
import win32com.axscript.client

import win32com.test.util
abstract type AbstractAXScript <: Abstractwin32com.test.util.TestCase end
verbose = "-v" in append!([PROGRAM_FILE], ARGS)
mutable struct AXScript <: AbstractAXScript
    verbose
end
function setUp(self::AXScript)
    file = GetFullPathName(win32api, join)
    self.verbose = verbose
    RegisterPythonServer(file, "python", self.verbose)
end

function testHost(self::AXScript)
    file = GetFullPathName(win32api, join)
    cmd = "%s \"%s\"" % (GetModuleFileName(win32api, 0), file)
    if verbose
        println("Testing Python Scripting host")
    end
    ExecuteShellCommand(win32com.test.util, cmd, self)
end

function testCScript(self::AXScript)
    file = GetFullPathName(win32api, join)
    cmd = "cscript.exe \"%s\"" % file
    if verbose
        println("Testing Windows Scripting host with Python script")
    end
    ExecuteShellCommand(win32com.test.util, cmd, self)
end

function main()
    testmain(win32com.test.util)
end

main()
end
