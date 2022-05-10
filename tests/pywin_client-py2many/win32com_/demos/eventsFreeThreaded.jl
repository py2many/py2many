module eventsFreeThreaded
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")

coinit_flags(sys) = 0


import win32event
import win32com.client

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
    rc = WaitForSingleObject(win32event, event(iexplore), 2000)
    if rc != win32event.WAIT_OBJECT_0
        println("Document load event FAILED to fire!!!")
    end
    Quit(iexplore)
    rc = WaitForSingleObject(win32event, event(iexplore), 2000)
    if rc != win32event.WAIT_OBJECT_0
        println("OnQuit event FAILED to fire!!!")
    end
    iexplore = nothing
    println("Finished the IE event sample!")
end

function main()
    TestExplorerEvents()
end

main()
end
