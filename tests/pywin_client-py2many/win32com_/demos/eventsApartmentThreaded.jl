module eventsApartmentThreaded
using Printf
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")


import win32com.client

import win32event


abstract type AbstractExplorerEvents end
mutable struct ExplorerEvents <: AbstractExplorerEvents
    event::Any

    ExplorerEvents(event::Any = CreateEvent(win32event, nothing, 0, 0, nothing)) =
        new(event)
end
function OnDocumentComplete(
    self::ExplorerEvents,
    pDisp = Empty(pythoncom),
    URL = Empty(pythoncom),
)
    thread = GetCurrentThreadId(win32api)
    @printf("OnDocumentComplete event processed on thread %d", thread)
    SetEvent(win32event, self.event)
end

function OnQuit(self::ExplorerEvents)
    thread = GetCurrentThreadId(win32api)
    @printf("OnQuit event processed on thread %d", thread)
    SetEvent(win32event, self.event)
end

function WaitWhileProcessingMessages(event, timeout = 2)::Bool
    start = clock(time)
    while true
        rc =
            MsgWaitForMultipleObjects(win32event, (event,), 0, 250, win32event.QS_ALLEVENTS)
        if rc == win32event.WAIT_OBJECT_0
            return true
        end
        if (clock(time) - start) > timeout
            return false
        end
        PumpWaitingMessages(pythoncom)
    end
end

function TestExplorerEvents()
    iexplore =
        DispatchWithEvents(win32com.client, "InternetExplorer.Application", ExplorerEvents)
    thread = GetCurrentThreadId(win32api)
    @printf("TestExplorerEvents created IE object on thread %d", thread)
    Visible(iexplore) = 1
    try
        Navigate(iexplore, GetFullPathName(win32api, "..\\readme.html"))
    catch exn
        let details = exn
            if details isa com_error(pythoncom)
                println("Warning - could not open the test HTML file", details)
            end
        end
    end
    if !WaitWhileProcessingMessages(event(iexplore))
        println("Document load event FAILED to fire!!!")
    end
    Quit(iexplore)
    if !WaitWhileProcessingMessages(event(iexplore))
        println("OnQuit event FAILED to fire!!!")
    end
    iexplore = nothing
end

function main()
    TestExplorerEvents()
end

main()
end
