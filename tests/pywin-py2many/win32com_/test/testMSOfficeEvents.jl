using PyCall
pythoncom = pyimport("pythoncom")
using win32com_.client: DispatchWithEvents, Dispatch
import msvcrt

import threading
stopEvent = Event(threading)
abstract type AbstractExcelEvents end
abstract type AbstractWorkbookEvents end
abstract type AbstractWordEvents end
function TestExcel()
    mutable struct ExcelEvents <: AbstractExcelEvents
    end
    function OnNewWorkbook(self::ExcelEvents, wb)
        if type_(wb) != types.InstanceType
            throw(
                RuntimeError(
                    "The transformer doesnt appear to have translated this for us!",
                ),
            )
        end
        self.seen_events["OnNewWorkbook"] = nothing
    end

    function OnWindowActivate(self::ExcelEvents, wb, wn)
        if type_(wb) != types.InstanceType || type_(wn) != types.InstanceType
            throw(
                RuntimeError(
                    "The transformer doesnt appear to have translated this for us!",
                ),
            )
        end
        self.seen_events["OnWindowActivate"] = nothing
    end

    function OnWindowDeactivate(self::ExcelEvents, wb, wn)
        self.seen_events["OnWindowDeactivate"] = nothing
    end

    function OnSheetDeactivate(self::ExcelEvents, sh)
        self.seen_events["OnSheetDeactivate"] = nothing
    end

    function OnSheetBeforeDoubleClick(self::ExcelEvents, Sh, Target, Cancel)::Int64
        if (Target.Column % 2) == 0
            println("You can double-click there...")
        else
            println("You can not double-click there...")
            return 1
        end
    end

    mutable struct WorkbookEvents <: AbstractWorkbookEvents
    end
    function OnActivate(self::WorkbookEvents)
        println("workbook OnActivate")
    end

    function OnBeforeRightClick(self::WorkbookEvents, Target, Cancel)
        println("It\'s a Worksheet Event")
    end

    e = DispatchWithEvents("Excel.Application", ExcelEvents)
    e.seen_events = Dict()
    e.Visible = 1
    book = Add(e.Workbooks)
    book = DispatchWithEvents(book, WorkbookEvents)
    println("Have book$(book)")
    println("Double-click in a few of the Excel cells...")
    println("Press any key when finished with Excel, or wait 10 seconds...")
    if !_WaitForFinish(e, 10)
        Quit(e)
    end
    if !_CheckSeenEvents(e, ["OnNewWorkbook", "OnWindowActivate"])
        quit(1)
    end
end

function TestWord()
    mutable struct WordEvents <: AbstractWordEvents
    end
    function OnDocumentChange(self::WordEvents)
        self.seen_events["OnDocumentChange"] = nothing
    end

    function OnWindowActivate(self::WordEvents, doc, wn)
        self.seen_events["OnWindowActivate"] = nothing
    end

    function OnQuit(self::WordEvents)
        self.seen_events["OnQuit"] = nothing
        set(stopEvent)
    end

    w = DispatchWithEvents("Word.Application", WordEvents)
    w.seen_events = Dict()
    w.Visible = 1
    Add(w.Documents)
    println("Press any key when finished with Word, or wait 10 seconds...")
    if !_WaitForFinish(w, 10)
        Quit(w)
    end
    if !_CheckSeenEvents(w, ["OnDocumentChange", "OnWindowActivate"])
        quit(1)
    end
end

function _WaitForFinish(ob, timeout)::Int64
    end_ = pylib::time() + timeout
    while true
        if kbhit(msvcrt)
            getch(msvcrt)
            has_break = true
            break
        end
        PumpWaitingMessages(pythoncom)
        wait(stopEvent, 0.2)
        if isSet(stopEvent)
            clear(stopEvent)
            has_break = true
            break
        end
        try
            if !(ob.Visible)
                return 0
            end
        catch exn
            if exn isa pythoncom.com_error
                #= pass =#
            end
        end
        if pylib::time() > end_
            return 0
        end
    end
    return 1
end

function _CheckSeenEvents(o, events)::Int64
    rc = 1
    for e in events
        if e ∉ o.seen_events
            println("ERROR: Expected event did not trigger$(e)")
            rc = 0
        end
    end
    return rc
end

function test()
    if "noword" ∉ append!([PROGRAM_FILE], ARGS)[2:end]
        TestWord()
    end
    if "noexcel" ∉ append!([PROGRAM_FILE], ARGS)[2:end]
        TestExcel()
    end
    println("Word and Excel event tests passed.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
end
