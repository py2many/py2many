module util
using Printf
using PyCall
pywintypes = pyimport("pywintypes")
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
using win32com.shell.shell: IsUserAnAdmin


import tempfile

import gc


import winerror

import win32com
import logging
import winreg
import io as StringIO
import pywin32_testutil
using pywin32_testutil: TestLoader, TestResult, TestRunner, LeakTestCase
abstract type AbstractFailed <: AbstractException end
abstract type AbstractCaptureWriter end
abstract type AbstractLogHandler <: Abstractlogging.Handler end
abstract type Abstract_CapturingFunctionTestCase end
abstract type AbstractShellTestCase end
function CheckClean()
try
exc_clear(sys)
catch exn
if exn isa AttributeError
#= pass =#
end
end
c = _GetInterfaceCount()
if c
@printf("Warning - %d com interface objects still alive", c)
end
c = _GetGatewayCount()
if c
@printf("Warning - %d com gateway objects still alive", c)
end
end

function RegisterPythonServer(filename, progids = nothing, verbose = 0)
if progids
if isa(progids, str)
progids = [progids]
end
why_not = nothing
for progid in progids
try
clsid = IID(pywintypes, progid)
catch exn
if exn isa com_error(pythoncom)
break;
end
end
try
HKCR = HKEY_CLASSES_ROOT(winreg)
hk = OpenKey(winreg, HKCR, "CLSID\\%s" % clsid)
dll = QueryValue(winreg, hk, "InprocServer32")
catch exn
if exn isa WindowsError
break;
end
end
ok_files = [basename(os.path, __file__(pythoncom)), "pythoncomloader%d%d.dll" % (version_info(sys)[1], version_info(sys)[2])]
if basename(os.path, dll) ∉ ok_files
why_not = "%r is registered against a different Python version (%s)" % (progid, dll)
break;
end
end
end
try
catch exn
if exn isa ImportError
println("Can\'t import win32com.shell - no idea if you are an admin or not?")
is_admin = false
end
end
if !(is_admin)
msg = "%r isn\'t registered, but I\'m not an administrator who can register it." % progids[1]
if why_not
msg += "\n(registration check failed as %s)" % why_not
end
throw(com_error(pythoncom, winerror.CO_E_CLASSSTRING, msg, nothing, -1))
end
cmd = "%s \"%s\" --unattended > nul 2>&1" % (GetModuleFileName(win32api, 0), filename)
if verbose
println("Registering engine", filename)
end
rc = system(os, cmd)
if rc
println("Registration command was:")
println(cmd)
throw(RuntimeError("Registration of engine \'%s\' failed" % filename))
end
end

function ExecuteShellCommand(cmd, testcase, expected_output = nothing, tracebacks_ok = 0)
output_name = mktemp(tempfile, "win32com_test")
cmd = cmd + (" > \"%s\" 2>&1" % output_name)
rc = system(os, cmd)
output = strip(read(readline(output_name)))
remove(os, output_name)
mutable struct Failed <: AbstractFailed

end

try
if rc
throw(Failed("exit code was " * string(rc)))
end
if expected_output != nothing && output != expected_output
throw(Failed("Expected output %r (got %r)" % (expected_output, output)))
end
if !(tracebacks_ok) && find(output, "Traceback (most recent call last)") >= 0
throw(Failed("traceback in program output"))
end
return output
catch exn
 let why = exn
if why isa Failed
@printf("Failed to exec command \'%r\'", cmd)
println("Failed as", why)
println("** start of program output **")
println(output)
println("** end of program output **")
fail(testcase, "Executing \'%s\' failed as %s" % (cmd, why))
end
end
end
end

function assertRaisesCOM_HRESULT(testcase, hresult, func)
try
func(args..., kw)
catch exn
 let details = exn
if details isa com_error(pythoncom)
if hresult(details) == hresult
return
end
end
end
end
fail(testcase, "Excepected COM exception with HRESULT 0x%x" % hresult)
end

mutable struct CaptureWriter <: AbstractCaptureWriter
captured::Any
old_out::Any
old_err::Any

            CaptureWriter(old_err = nothing) = begin
                self.clear()
                new(old_err )
            end
end
function capture(self::CaptureWriter)
clear(self)
self.old_out = stdout(sys)
self.old_err = stderr(sys)
stdout(sys) = self
stderr(sys) = self
end

function release(self::CaptureWriter)
if self.old_out
stdout(sys) = self.old_out
self.old_out = nothing
end
if self.old_err
stderr(sys) = self.old_err
self.old_err = nothing
end
end

function clear(self::CaptureWriter)
self.captured = []
end

function write(self::CaptureWriter, msg)
append(self.captured, msg)
end

function get_captured(self::CaptureWriter)
return join(self.captured, "")
end

function get_num_lines_captured(self::CaptureWriter)::Int64
return length(split(join(self.captured, ""), "\n"))
end

mutable struct LogHandler <: AbstractLogHandler
emitted::Vector

            LogHandler(emitted::Vector = []) = begin
                logging.Handler.__init__(self)
                new(emitted)
            end
end
function emit(self::LogHandler, record)
append(self.emitted, record)
end

_win32com_logger = nothing
function setup_test_logger()::Tuple
old_log = getattr(win32com, "logger", nothing)
global _win32com_logger
if _win32com_logger === nothing
_win32com_logger = Logger(logging, "test")
handler = LogHandler()
addHandler(_win32com_logger, handler)
end
win32com.logger = _win32com_logger
handler = handlers(_win32com_logger)[1]
emitted(handler) = []
return (emitted(handler), old_log)
end

function restore_test_logger(prev_logger)
@assert(prev_logger === nothing)
if prev_logger === nothing
#Delete Unsupported
del(win32com.logger)
else
win32com.logger = prev_logger
end
end

TestCase = TestCase(unittest)
function CapturingFunctionTestCase()
real_test = _CapturingFunctionTestCase(args..., kw)
return LeakTestCase(real_test)
end

mutable struct _CapturingFunctionTestCase <: Abstract_CapturingFunctionTestCase

end
function __call__(self::_CapturingFunctionTestCase, result = nothing)
if result === nothing
result = defaultTestResult(self)
end
writer = CaptureWriter()
capture(writer)
try
__call__(unittest.FunctionTestCase, self)
if getattr(self, "do_leak_tests", 0) && hasattr(sys, "gettotalrefcount")
run_leak_tests(self, result)
end
finally
release(writer)
end
output = get_captured(writer)
checkOutput(self, output, result)
if showAll(result)
println(output)
end
end

function checkOutput(self::_CapturingFunctionTestCase, output, result)
if find(output, "Traceback") >= 0
msg = "Test output contained a traceback\n---\n%s\n---" % output
append(result.errors, (self, msg))
end
end

mutable struct ShellTestCase <: AbstractShellTestCase
__cmd::Any
__eo::Any

            ShellTestCase(cmd, expected_output, __cmd = cmd, __eo = expected_output) = begin
                unittest.TestCase.__init__(self)
                new(cmd, expected_output, __cmd , __eo )
            end
end
function runTest(self::ShellTestCase)
ExecuteShellCommand(self.__cmd, self, self.__eo)
end

function __str__(self::ShellTestCase)::String
max = 30
if length(self.__cmd) > max
cmd_repr = self.__cmd[begin:max] + "..."
else
cmd_repr = self.__cmd
end
return "exec: " + cmd_repr
end

function testmain()
testmain()
CheckClean()
end

end