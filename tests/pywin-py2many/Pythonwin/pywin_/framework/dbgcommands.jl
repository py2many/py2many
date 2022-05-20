using PyCall
win32ui = pyimport("win32ui")
import win32com_.gen_py.debugger
import win32com_.gen_py.framework.editor.color.coloreditor
import win32com_.gen_py.framework.editor
import win32con
include("scriptutils.jl")
import warnings
using win32com_.gen_py.scintilla.control: CScintillaEditInterface
IdToBarNames = Dict(
    win32ui.IDC_DBG_STACK => ("Stack", 0),
    win32ui.IDC_DBG_BREAKPOINTS => ("Breakpoints", 0),
    win32ui.IDC_DBG_WATCH => ("Watch", 1),
)
mutable struct DebuggerCommandHandler <: AbstractDebuggerCommandHandler
    OnDebuggerBar
    OnUpdateDebuggerBar
end
function HookCommands(self::DebuggerCommandHandler)
    commands = (
        (self.OnStep, nothing, win32ui.IDC_DBG_STEP),
        (self.OnStepOut, self.OnUpdateOnlyBreak, win32ui.IDC_DBG_STEPOUT),
        (self.OnStepOver, nothing, win32ui.IDC_DBG_STEPOVER),
        (self.OnGo, nothing, win32ui.IDC_DBG_GO),
        (self.OnClose, self.OnUpdateClose, win32ui.IDC_DBG_CLOSE),
        (self.OnAdd, self.OnUpdateAddBreakpoints, win32ui.IDC_DBG_ADD),
        (self.OnClearAll, self.OnUpdateClearAllBreakpoints, win32ui.IDC_DBG_CLEAR),
    )
    frame = GetMainFrame(win32ui)
    for (methHandler, methUpdate, id) in commands
        HookCommand(frame, methHandler, id)
        if !(methUpdate === nothing)
            HookCommandUpdate(frame, methUpdate, id)
        end
    end
    for id in collect(keys(IdToBarNames))
        HookCommand(frame, self.OnDebuggerBar, id)
        HookCommandUpdate(frame, self.OnUpdateDebuggerBar, id)
    end
end

function OnDebuggerToolbar(self::DebuggerCommandHandler, id, code)
    if code == 0
        return !OnBarCheck(GetMainFrame(win32ui), id)
    end
end

function OnUpdateDebuggerToolbar(self::DebuggerCommandHandler, cmdui)
    OnUpdateControlBarMenu(GetMainFrame(win32ui), cmdui)
    Enable(cmdui, 1)
end

function _GetDebugger(self::DebuggerCommandHandler)
    try
        return win32com_.gen_py.debugger.currentDebugger
    catch exn
        if exn isa ImportError
            return nothing
        end
    end
end

function _DoOrStart(self::DebuggerCommandHandler, doMethod, startFlag)
    d = _GetDebugger(self)
    if d != nothing && IsDebugging(d)
        method = getfield(d, :doMethod)
        method()
    else
        RunScript(scriptutils, nothing, nothing, 0, startFlag)
    end
end

function OnStep(self::DebuggerCommandHandler, msg, code)
    _DoOrStart(self, "do_set_step", scriptutils.RS_DEBUGGER_STEP)
end

function OnStepOver(self::DebuggerCommandHandler, msg, code)
    _DoOrStart(self, "do_set_next", scriptutils.RS_DEBUGGER_STEP)
end

function OnStepOut(self::DebuggerCommandHandler, msg, code)
    d = _GetDebugger(self)
    if d != nothing && IsDebugging(d)
        do_set_return(d)
    end
end

function OnGo(self::DebuggerCommandHandler, msg, code)
    _DoOrStart(self, "do_set_continue", scriptutils.RS_DEBUGGER_GO)
end

function OnClose(self::DebuggerCommandHandler, msg, code)
    d = _GetDebugger(self)
    if d != nothing
        if IsDebugging(d)
            set_quit(d)
        else
            close(d)
        end
    end
end

function OnUpdateClose(self::DebuggerCommandHandler, cmdui)
    d = _GetDebugger(self)
    if d != nothing && d.inited
        Enable(cmdui, 1)
    else
        Enable(cmdui, 0)
    end
end

function OnAdd(self::DebuggerCommandHandler, msg, code)
    doc, view = GetActiveEditorDocument(scriptutils)
    if doc === nothing
        warn(warnings, "There is no active window - no breakpoint can be added")
        return nothing
    end
    pathName = GetPathName(doc)
    lineNo = LineFromChar(view, GetSel(view)[1]) + 1
    d = _GetDebugger(self)
    if d === nothing
        MarkerToggle(
            doc,
            lineNo,
            win32com_.gen_py.framework.editor.color.coloreditor.MARKER_BREAKPOINT,
        )
    else
        if get_break(d, pathName, lineNo)
            SetStatusText(win32ui, "Clearing breakpoint", 1)
            rc = clear_break(d, pathName, lineNo)
        else
            SetStatusText(win32ui, "Setting breakpoint", 1)
            rc = set_break(d, pathName, lineNo)
        end
        if rc
            MessageBox(win32ui, rc)
        end
        GUIRespondDebuggerData(d)
    end
end

function OnClearAll(self::DebuggerCommandHandler, msg, code)
    SetStatusText(win32ui, "Clearing all breakpoints")
    d = _GetDebugger(self)
    if d === nothing
        for doc in GetDocumentList(win32com_.gen_py.framework.editor.editorTemplate)
            MarkerDeleteAll(
                doc,
                win32com_.gen_py.framework.editor.color.coloreditor.MARKER_BREAKPOINT,
            )
        end
    else
        clear_all_breaks(d)
        UpdateAllLineStates(d)
        GUIRespondDebuggerData(d)
    end
end

function OnUpdateOnlyBreak(self::DebuggerCommandHandler, cmdui)
    d = _GetDebugger(self)
    ok = d != nothing && IsBreak(d)
    Enable(cmdui, ok)
end

function OnUpdateAddBreakpoints(self::DebuggerCommandHandler, cmdui)
    doc, view = GetActiveEditorDocument(scriptutils)
    if doc === nothing || !isa(view, CScintillaEditInterface)
        enabled = 0
    else
        enabled = 1
        lineNo = LineFromChar(view, GetSel(view)[1]) + 1
        SetCheck(
            cmdui,
            MarkerAtLine(
                doc,
                lineNo,
                win32com_.gen_py.framework.editor.color.coloreditor.MARKER_BREAKPOINT,
            ) != 0,
        )
    end
    Enable(cmdui, enabled)
end

function OnUpdateClearAllBreakpoints(self::DebuggerCommandHandler, cmdui)
    d = _GetDebugger(self)
    Enable(cmdui, d === nothing || length(d.breaks) != 0)
end

function OnUpdateDebuggerBar(self::DebuggerCommandHandler, cmdui)
    name, always = get(IdToBarNames, cmdui.m_nID)
    enabled = always
    d = _GetDebugger(self)
    if d != nothing && IsDebugging(d) && name != nothing
        enabled = 1
        bar = GetDebuggerBar(d, name)
        SetCheck(cmdui, IsWindowVisible(bar))
    end
    Enable(cmdui, enabled)
end

function OnDebuggerBar(self::DebuggerCommandHandler, id, code)
    name = get(IdToBarNames, id)[1]
    d = _GetDebugger(self)
    if d != nothing && name != nothing
        bar = GetDebuggerBar(d, name)
        newState = !IsWindowVisible(bar)
        ShowControlBar(GetMainFrame(win32ui), bar, newState, 1)
    end
end

abstract type AbstractDebuggerCommandHandler end
