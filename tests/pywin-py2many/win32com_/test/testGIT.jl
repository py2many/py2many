#= Testing pasing object between multiple COM threads

Uses standard COM marshalling to pass objects between threads.  Even 
though Python generally seems to work when you just pass COM objects
between threads, it shouldnt.

This shows the "correct" way to do it.

It shows that although we create new threads to use the Python.Interpreter,
COM marshalls back all calls to that object to the main Python thread,
which must be running a message loop (as this sample does).

When this test is run in "free threaded" mode (at this stage, you must 
manually mark the COM objects as "ThreadingModel=Free", or run from a 
service which has marked itself as free-threaded), then no marshalling
is done, and the Python.Interpreter object start doing the "expected" thing
- ie, it reports being on the same thread as its caller!

Python.exe needs a good way to mark itself as FreeThreaded - at the moment
this is a pain in the but!

 =#
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import winerror
import _thread
import win32com_.client
import win32event

function TestInterp(interp)
    if Eval(interp, "1+1") != 2
        throw(ValueError("The interpreter returned the wrong result."))
    end
    try
        Eval(interp, 1 + 1)
        throw(ValueError("The interpreter did not raise an exception"))
    catch exn
        let details = exn
            if details isa pythoncom.com_error
                if details[1] != winerror.DISP_E_TYPEMISMATCH
                    throw(
                        ValueError(
                            "The interpreter exception was not winerror.DISP_E_TYPEMISMATCH.",
                        ),
                    )
                end
            end
        end
    end
end

function TestInterpInThread(stopEvent, cookie)
    try
        DoTestInterpInThread(cookie)
    finally
        SetEvent(win32event, stopEvent)
    end
end

function CreateGIT()
    return CoCreateInstance(
        pythoncom,
        pythoncom.CLSID_StdGlobalInterfaceTable,
        nothing,
        pythoncom.CLSCTX_INPROC,
        pythoncom.IID_IGlobalInterfaceTable,
    )
end

function DoTestInterpInThread(cookie)
    try
        CoInitialize(pythoncom)
        myThread = GetCurrentThreadId(win32api)
        GIT = CreateGIT()
        interp = GetInterfaceFromGlobal(GIT, cookie, pythoncom.IID_IDispatch)
        interp = Dispatch(win32com_.client, interp)
        TestInterp(interp)
        Exec(interp, "import win32api")
        @printf(
            "The test thread id is %d, Python.Interpreter\'s thread ID is %d\n",
            myThread,
            Eval(interp, "win32api.GetCurrentThreadId()")
        )
        interp = nothing
        CoUninitialize(pythoncom)
    catch exn
        current_exceptions() != [] ? current_exceptions()[end] : nothing
    end
end

function BeginThreadsSimpleMarshal(numThreads, cookie)::Vector
    #= Creates multiple threads using simple (but slower) marshalling.

        Single interpreter object, but a new stream is created per thread.

        Returns the handles the threads will set when complete.
         =#
    ret = []
    for i = 0:numThreads-1
        hEvent = CreateEvent(win32event, nothing, 0, 0, nothing)
        start_new(_thread, TestInterpInThread, (hEvent, cookie))
        push!(ret, hEvent)
    end
    return ret
end

function test(fn)
    @printf("The main thread is %d\n", GetCurrentThreadId(win32api))
    GIT = CreateGIT()
    interp = Dispatch(win32com_.client, "Python.Interpreter")
    cookie = RegisterInterfaceInGlobal(GIT, interp._oleobj_, pythoncom.IID_IDispatch)
    events = fn(4, cookie)
    numFinished = 0
    while true
        try
            rc = MsgWaitForMultipleObjects(
                win32event,
                events,
                0,
                2000,
                win32event.QS_ALLINPUT,
            )
            if rc >= win32event.WAIT_OBJECT_0 &&
               rc < (win32event.WAIT_OBJECT_0 + length(events))
                numFinished = numFinished + 1
                if numFinished >= length(events)
                    has_break = true
                    break
                end
            elseif rc == (win32event.WAIT_OBJECT_0 + length(events))
                PumpWaitingMessages(pythoncom)
            else
                @printf(
                    "Waiting for thread to stop with interfaces=%d, gateways=%d\n",
                    _GetInterfaceCount(pythoncom),
                    _GetGatewayCount(pythoncom)
                )
            end
        catch exn
            if exn isa KeyboardInterrupt
                break
            end
        end
    end
    RevokeInterfaceFromGlobal(GIT, cookie)
    #Delete Unsupported
    del(interp)
    #Delete Unsupported
    del(GIT)
end

if abspath(PROGRAM_FILE) == @__FILE__
    test(BeginThreadsSimpleMarshal)
    Sleep(win32api, 500)
    CoUninitialize(pythoncom)
    if _GetInterfaceCount(pythoncom) != 0 || _GetGatewayCount(pythoncom) != 0
        @printf(
            "Done with interfaces=%d, gateways=%d\n",
            _GetInterfaceCount(pythoncom),
            _GetGatewayCount(pythoncom)
        )
    else
        println("Done.")
    end
end
