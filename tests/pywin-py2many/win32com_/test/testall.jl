using Getopt
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
include("GenTestScripts.jl")
import shutil
import win32com_.client.gencache
using win32com_.test: pippo_server
import string
import getopt
try
    this_file = __file__
catch exn
    if exn isa NameError
        this_file = append!([PROGRAM_FILE], ARGS)[1]
    end
end
win32com_src_dir = abspath(os.path, join)
import win32com_
win32com_.__path__[1] = win32com_src_dir
abstract type AbstractPyCOMTest <: AbstractTestCase end
abstract type AbstractPippoTest <: AbstractTestCase end

import win32com_.client
using win32com_.test.util:
    CheckClean,
    TestCase,
    CapturingFunctionTestCase,
    ShellTestCase,
    TestLoader,
    TestRunner,
    RegisterPythonServer
verbosity = 1
function GenerateAndRunOldStyle()
    GenerateAll(GenTestScripts)
    try
        #= pass =#
    finally
        CleanAll(GenTestScripts)
    end
end

function CleanGenerated()
    if isdir(os.path, win32com_.__gen_path__)
        if verbosity > 1
            @printf("Deleting files from %s\n", win32com_.__gen_path__)
        end
        rmtree(shutil, win32com_.__gen_path__)
    end
    __init__(win32com_.client.gencache)
end

function RemoveRefCountOutput(data)::String
    while true
        last_line_pos = rfind(data, "\n")
        if !match(re, "\\[\\d+ refs\\]", data[last_line_pos+2:end])
            has_break = true
            break
        end
        if last_line_pos < 0
            return ""
        end
        data = data[begin:last_line_pos]
    end
    return data
end

function ExecuteSilentlyIfOK(cmd, testcase)::String
    f = popen(os, cmd)
    data = strip(read(f))
    rc = close(f)
    if rc
        println(data)
        fail(testcase, "Executing \'%s\' failed (%d)" % (cmd, rc))
    end
    return RemoveRefCountOutput(data)
end

mutable struct PyCOMTest <: AbstractPyCOMTest
    no_leak_tests::Bool

    PyCOMTest(no_leak_tests::Bool = true) = new(no_leak_tests)
end
function testit(self::PyCOMTest)
    RegisterPythonServer(join, "Python.Test.PyCOMTest")
    fname = join
    cmd = "%s \"%s\" -q 2>&1" % (sys.executable, fname)
    data = ExecuteSilentlyIfOK(cmd, self)
end

mutable struct PippoTest <: AbstractPippoTest
end
function testit(self::PippoTest)
    RegisterPythonServer(pippo_server.__file__, "Python.Test.Pippo")
    python = sys.executable
    fname = join
    cmd = "%s \"%s\" 2>&1" % (python, fname)
    ExecuteSilentlyIfOK(cmd, self)
end

unittest_modules = [
    split(
        "testIterators testvbscript_regexp testStorage\n          testStreams testWMI policySemantics testShell testROT\n          testxslt testCollections\n          errorSemantics.test testArrays\n          testClipboard\n          testConversionErrors\n        ",
    ),
    split("\n        testAXScript testDictionary testServers testvb testMarshal\n        "),
    split(
        "testMSOffice.TestAll testMSOfficeEvents.test testAccess.test\n           testExplorer.TestAll testExchange.test\n        ",
    ),
    split("testmakepy.TestAll\n        "),
]
unittest_other_modules = [split("win32com_.directsound.test.ds_test\n        "), [], [], []]
output_checked_programs = [
    [],
    [
        ("cscript.exe /nologo //E:vbscript testInterp.vbs", "VBScript test worked OK"),
        (
            "cscript.exe /nologo //E:vbscript testDictionary.vbs",
            "VBScript has successfully tested Python.Dictionary",
        ),
    ],
    [],
    [],
]
custom_test_cases = [[], [PyCOMTest, PippoTest], [], []]
function get_test_mod_and_func(test_name, import_failures)::Tuple
    if find(test_name, ".") > 0
        mod_name, func_name = split(test_name, ".")
    else
        mod_name = test_name
        func_name = nothing
    end
    fq_mod_name = "win32com_.test." + mod_name
    try
        __import__(fq_mod_name)
        mod = sys.modules[fq_mod_name+1]
    catch exn
        append(import_failures, (mod_name, exc_info(sys)[begin:2]))
        return (nothing, nothing)
    end
    func = func_name === nothing ? (nothing) : (getfield(mod, :func_name))
    return (mod, func)
end

function make_test_suite(test_level = 1)
    suite = TestSuite(unittest)
    import_failures = []
    loader = TestLoader()
    for i = 0:testLevel-1
        for mod_name in unittest_modules[i+1]
            mod, func = get_test_mod_and_func(mod_name, import_failures)
            if mod === nothing
                throw(Exception("no such module \'$()\'"))
            end
            if func != nothing
                test = CapturingFunctionTestCase(func, mod_name)
            elseif hasfield(typeof(mod), :suite)
                test = suite(mod)
            else
                test = loadTestsFromModule(loader, mod)
            end
            @assert(countTestCases(test) > 0)
            addTest(suite, test)
        end
        for (cmd, output) in output_checked_programs[i+1]
            addTest(suite, ShellTestCase(cmd, output))
        end
        for test_class in custom_test_cases[i+1]
            addTest(suite, loadTestsFromTestCase(unittest.defaultTestLoader, test_class))
        end
    end
    for i = 0:testLevel-1
        for mod_name in unittest_other_modules[i+1]
            try
                __import__(mod_name)
            catch exn
                push!(import_failures, (mod_name, exc_info(sys)[begin:2]))
                continue
            end
            mod = sys.modules[mod_name+1]
            if hasfield(typeof(mod), :suite)
                test = suite(mod)
            else
                test = loadTestsFromModule(loader, mod)
            end
            @assert(countTestCases(test) > 0)
            addTest(suite, test)
        end
    end
    return (suite, import_failures)
end

function usage(why)
    println(why)
    println()
    println("win32com_ test suite")
    println("usage: testall [-v] test_level")
    println("  where test_level is an integer 1-3.  Level 1 tests are quick,")
    println("  level 2 tests invoke Word, IE etc, level 3 take ages!")
    quit(1)
end

if abspath(PROGRAM_FILE) == @__FILE__
    try
        opts, args = getopt(getopt, append!([PROGRAM_FILE], ARGS)[2:end], "v")
    catch exn
        let why = exn
            if why isa getopt.error
                usage(why)
            end
        end
    end
    for (opt, val) in opts
        if opt == "-v"
            verbosity += 1
        end
    end
    testLevel = 2
    test_names = []
    for arg in args
        try
            testLevel = parse(Int, arg)
            if testLevel < 0 || testLevel > 4
                throw(ValueError("Only levels 1-4 are supported"))
            end
        catch exn
            if exn isa ValueError
                push!(test_names, arg)
            end
        end
    end
    if test_names
        usage("Test names are not supported yet")
    end
    CleanGenerated()
    suite, import_failures = make_test_suite(testLevel)
    if verbosity != 0
        if hasfield(typeof(sys), :gettotalrefcount)
            println("This is a debug build - memory leak tests will also be run.")
            println("These tests may take *many* minutes to run - be patient!")
            println("(running from python.exe will avoid these leak tests)")
        end
        @printf(
            "Executing level %d tests - %d test cases will be run\n",
            testLevel,
            countTestCases(suite)
        )
        if verbosity == 1 && countTestCases(suite) < 70
            println("")
        end
    end
    testRunner = TestRunner(verbosity)
    testResult = run(testRunner, suite)
    if import_failures
        writeln(
            testResult.stream,
            "*** The following test modules could not be imported ***",
        )
        for (mod_name, (exc_type, exc_val)) in import_failures
            desc = join(format_exception_only(traceback, exc_type, exc_val), "\n")
            write(testResult.stream, "%s: %s" % (mod_name, desc))
        end
        writeln(
            testResult.stream,
            "*** %d test(s) could not be run ***" % length(import_failures),
        )
    end
    if !wasSuccessful(testResult)
        println("- unittest tests FAILED")
    end
    CheckClean()
    CoUninitialize(pythoncom)
    CleanGenerated()
    if !wasSuccessful(testResult)
        quit(1)
    end
end
