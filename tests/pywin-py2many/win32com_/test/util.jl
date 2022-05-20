using Printf
using PyCall
pythoncom = pyimport("pythoncom")
pywintypes = pyimport("pywintypes")
win32api = pyimport("win32api")
using win32com_.shell.shell: IsUserAnAdmin

import tempfile

import gc

import winerror

import win32com_
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
        @printf("Warning - %d com interface objects still alive\n", c)
    end
    c = _GetGatewayCount()
    if c
        @printf("Warning - %d com gateway objects still alive\n", c)
    end
end

function RegisterPythonServer(filename, progids = nothing, verbose = 0)
    if progids
        if isa(progids, str)
            progids = [progids]
        end
        why_not = nothing
        has_break = false
        for progid in progids
            try
                clsid = IID(pywintypes, progid)
            catch exn
                if exn isa pythoncom.com_error
                    break
                end
            end
            try
                HKCR = winreg.HKEY_CLASSES_ROOT
                hk = OpenKey(winreg, HKCR, "CLSID\\%s" % clsid)
                dll = QueryValue(winreg, hk, "InprocServer32")
            catch exn
                if exn isa WindowsError
                    break
                end
            end
            ok_files = [
                basename(os.path, pythoncom.__file__),
                "pythoncomloader%d%d.dll" % (sys.version_info[1], sys.version_info[2]),
            ]
            if basename(os.path, dll) ∉ ok_files
                why_not =
                    "%r is registered against a different Python version (%s)" %
                    (progid, dll)
                has_break = true
                break
            end
        end
        if has_break != true
            return
        end
    end
    try
    catch exn
        if exn isa ImportError
            println("Can\'t import win32com_.shell - no idea if you are an admin or not?")
            is_admin = false
        end
    end
    if !(is_admin)
        msg =
            "%r isn\'t registered, but I\'m not an administrator who can register it." %
            progids[1]
        if why_not
            msg += "\n(registration check failed as %s)" % why_not
        end
        throw(com_error(pythoncom, winerror.CO_E_CLASSSTRING, msg, nothing, -1))
    end
    cmd = "%s \"%s\" --unattended > nul 2>&1" % (GetModuleFileName(win32api, 0), filename)
    if verbose
        println("Registering engine$(filename)")
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
                @printf("Failed to exec command \'%r\'\n", cmd)
                println("Failed as$(why)")
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
            if details isa pythoncom.com_error
                if details.hresult == hresult
                    return
                end
            end
        end
    end
    fail(testcase, "Excepected COM exception with HRESULT 0x%x" % hresult)
end

mutable struct CaptureWriter <: AbstractCaptureWriter
    old_err
    old_out
    captured::Vector

    CaptureWriter() = begin
        clear()
        new()
    end
end
function capture(self::CaptureWriter)
    clear(self)
    self.old_out = sys.stdout
    self.old_err = sys.stderr
    sys.stdout = self
    sys.stderr = self
end

function release(self::CaptureWriter)
    if self.old_out
        sys.stdout = self.old_out
        self.old_out = nothing
    end
    if self.old_err
        sys.stderr = self.old_err
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

    LogHandler() = begin
        logging.Handler.__init__(self)
        new()
    end
end
function emit(self::LogHandler, record)
    append(self.emitted, record)
end

_win32com_logger = nothing
function setup_test_logger()::Tuple
    old_log =
        (hasfield(typeof(win32com_), :logger) ? getfield(win32com_, :logger) : nothing)
    global _win32com_logger
    if _win32com_logger === nothing
        _win32com_logger = Logger(logging, "test")
        handler = LogHandler()
        addHandler(_win32com_logger, handler)
    end
    win32com_.logger = _win32com_logger
    handler = _win32com_logger.handlers[1]
    handler.emitted = []
    return (handler.emitted, old_log)
end

function restore_test_logger(prev_logger)
    @assert(prev_logger === nothing)
    if prev_logger === nothing
        #Delete Unsupported
        del(win32com_.logger)
    else
        win32com_.logger = prev_logger
    end
end

TestCase = unittest.TestCase
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
        if (hasfield(typeof(self), :do_leak_tests) ? getfield(self, :do_leak_tests) : 0) &&
           hasfield(typeof(sys), :gettotalrefcount)
            run_leak_tests(self, result)
        end
    finally
        release(writer)
    end
    output = get_captured(writer)
    checkOutput(self, output, result)
    if result.showAll
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
    __cmd
    __eo

    ShellTestCase(cmd, expected_output) = begin
        unittest.TestCase.__init__(self)
        new(cmd, expected_output)
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
