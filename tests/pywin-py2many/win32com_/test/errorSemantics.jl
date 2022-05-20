using PyCall
pythoncom = pyimport("pythoncom")
import win32com_
using win32com_.test.util: CheckClean

using win32com_.server.exception: COMException
using win32com_.server.util: wrap
using win32com_.client: Dispatch
import winerror
using win32com_.test.util: CaptureWriter
mutable struct error <: Abstracterror
    com_exception

    error(msg, com_exception = nothing) = begin
        Exception.__init__(self, msg, string(com_exception))
        new(msg, com_exception)
    end
end

abstract type Abstracterror <: AbstractException end
abstract type AbstractTestServer end
abstract type AbstractTestLogHandler <: Abstractlogging.Handler end
mutable struct TestServer <: AbstractTestServer
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    TestServer(
        _com_interfaces_::Vector = [pythoncom.IID_IStream],
        _public_methods_::Vector{String} = ["Clone", "Commit", "LockRegion", "Read"],
    ) = new(_com_interfaces_, _public_methods_)
end
function Clone(self::TestServer)
    throw(COMException("Not today", winerror.E_UNEXPECTED))
end

function Commit(self::TestServer, flags)
    if flags == 0
        throw(Exception("😀"))
    end
    excepinfo = (winerror.E_UNEXPECTED, "source", "😀", "helpfile", 1, winerror.E_FAIL)
    throw(com_error(pythoncom, winerror.E_UNEXPECTED, "desc", excepinfo, nothing))
end

function test()
    com_server = wrap(TestServer(), pythoncom.IID_IStream)
    try
        Clone(com_server)
        throw(error("Expecting this call to fail!"))
    catch exn
        let com_exc = exn
            if com_exc isa pythoncom.com_error
                if com_exc.hresult != winerror.E_UNEXPECTED
                    throw(
                        error(
                            "Calling the object natively did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                exc = com_exc.excepinfo
                if !(exc) || exc[end] != winerror.E_UNEXPECTED
                    throw(
                        error(
                            "The scode element of the exception tuple did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                if exc[3] != "Not today"
                    throw(
                        error(
                            "The description in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
            end
        end
    end
    cap = CaptureWriter()
    try
        capture(cap)
        try
            Commit(com_server, 0)
        finally
            release(cap)
        end
        throw(error("Expecting this call to fail!"))
    catch exn
        let com_exc = exn
            if com_exc isa pythoncom.com_error
                if com_exc.hresult != winerror.E_FAIL
                    throw(
                        error("The hresult was not E_FAIL for an internal error", com_exc),
                    )
                end
                if com_exc.excepinfo[2] != "Python COM Server Internal Error"
                    throw(
                        error(
                            "The description in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
            end
        end
    end
    if find(get_captured(cap), "Traceback") < 0
        throw(error("Could not find a traceback in stderr: %r" % (get_captured(cap),)))
    end
    com_server = Dispatch(wrap(TestServer()))
    try
        Clone(com_server)
        throw(error("Expecting this call to fail!"))
    catch exn
        let com_exc = exn
            if com_exc isa pythoncom.com_error
                if com_exc.hresult != winerror.DISP_E_EXCEPTION
                    throw(
                        error(
                            "Calling the object via IDispatch did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                exc = com_exc.excepinfo
                if !(exc) || exc[end] != winerror.E_UNEXPECTED
                    throw(
                        error(
                            "The scode element of the exception tuple did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                if exc[3] != "Not today"
                    throw(
                        error(
                            "The description in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
            end
        end
    end
    clear(cap)
    try
        capture(cap)
        try
            Commit(com_server, 0)
        finally
            release(cap)
        end
        throw(error("Expecting this call to fail!"))
    catch exn
        let com_exc = exn
            if com_exc isa pythoncom.com_error
                if com_exc.hresult != winerror.DISP_E_EXCEPTION
                    throw(
                        error(
                            "Calling the object via IDispatch did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                exc = com_exc.excepinfo
                if !(exc) || exc[end] != winerror.E_FAIL
                    throw(
                        error(
                            "The scode element of the exception tuple did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                if exc[2] != "Python COM Server Internal Error"
                    throw(
                        error(
                            "The description in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
            end
        end
    end
    if find(get_captured(cap), "Traceback") < 0
        throw(error("Could not find a traceback in stderr: %r" % (get_captured(cap),)))
    end
    clear(cap)
    try
        capture(cap)
        try
            Commit(com_server, 1)
        finally
            release(cap)
        end
        throw(error("Expecting this call to fail!"))
    catch exn
        let com_exc = exn
            if com_exc isa pythoncom.com_error
                if com_exc.hresult != winerror.DISP_E_EXCEPTION
                    throw(
                        error(
                            "Calling the object via IDispatch did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                exc = com_exc.excepinfo
                if !(exc) || exc[end] != winerror.E_FAIL
                    throw(
                        error(
                            "The scode element of the exception tuple did not yield the correct scode",
                            com_exc,
                        ),
                    )
                end
                if exc[2] != "source"
                    throw(
                        error(
                            "The source in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
                if exc[3] != "😀"
                    throw(
                        error(
                            "The description in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
                if exc[4] != "helpfile"
                    throw(
                        error(
                            "The helpfile in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
                if exc[5] != 1
                    throw(
                        error(
                            "The help context in the exception tuple did not yield the correct string",
                            com_exc,
                        ),
                    )
                end
            end
        end
    end
end

try
    import logging
catch exn
    if exn isa ImportError
        logging = nothing
    end
end
if logging != nothing
    mutable struct TestLogHandler <: AbstractTestLogHandler
        num_emits::Int64
        last_record

        TestLogHandler() = begin
            reset()
            logging.Handler.__init__(self)
            new()
        end
    end
    function reset(self::TestLogHandler)
        self.num_emits = 0
        self.last_record = nothing
    end

    function emit(self::TestLogHandler, record)
        self.num_emits += 1
        self.last_record = self
        return
        println("--- record start")
        println(self.last_record)
        println("--- record end")
    end

    function testLogger()
        @assert(!hasfield(typeof(win32com_), :logger))
        handler = TestLogHandler()
        formatter = Formatter(logging, "%(message)s")
        setFormatter(handler, formatter)
        log = getLogger(logging, "win32com_test")
        addHandler(log, handler)
        win32com_.logger = log
        com_server = wrap(TestServer(), pythoncom.IID_IStream)
        try
            Commit(com_server, 0)
            throw(RuntimeError("should have failed"))
        catch exn
            let exc = exn
                if exc isa pythoncom.error
                    message = exc.excepinfo[3]
                    @assert(endswith(message, "Exception: 😀\n"))
                end
            end
        end
        @assert(handler.num_emits == 1)
        @assert(
            startswith(
                handler.last_record,
                "pythoncom error: Unexpected exception in gateway method \'Commit\'",
            )
        )
        reset(handler)
        com_server = Dispatch(wrap(TestServer()))
        try
            Commit(com_server, 0)
            throw(RuntimeError("should have failed"))
        catch exn
            let exc = exn
                if exc isa pythoncom.error
                    message = exc.excepinfo[3]
                    @assert(endswith(message, "Exception: 😀\n"))
                end
            end
        end
        @assert(handler.num_emits == 1)
        reset(handler)
    end
end
if abspath(PROGRAM_FILE) == @__FILE__
    test()
    if logging != nothing
        testLogger()
    end
    CheckClean()
    println("error semantic tests worked")
end
