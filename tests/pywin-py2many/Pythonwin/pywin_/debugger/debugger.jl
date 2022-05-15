module debugger
using Printf
using PyCall
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")
using bdb: Breakpoint
import __main__
import linecache
import pdb
import bdb

import string

import win32con
import win32com_.gen_py.docking.DockingBar
using win32com_.gen_py.mfc: dialog, object, afxres, window
using win32com_.gen_py.framework: app, interact, editor, scriptutils
using win32com_.gen_py.framework.editor.color.coloreditor: MARKER_CURRENT, MARKER_BREAKPOINT
using win32com_.gen_py.tools: browser, hierlist
import commctrl

if win32ui.UNICODE
    LVN_ENDLABELEDIT = commctrl.LVN_ENDLABELEDITW
else
    LVN_ENDLABELEDIT = commctrl.LVN_ENDLABELEDITA
end
using dbgcon: *
error = "win32com_.gen_py.debugger.error"
function SetInteractiveContext(globs, locs)
    if interact.edit != nothing && interact.edit.currentView != nothing
        SetContext(interact.edit.currentView, globs, locs)
    end
end

abstract type AbstractHierListItem <: Abstractbrowser.HLIPythonObject end
abstract type AbstractHierFrameItem <: AbstractHierListItem end
abstract type AbstractHierFrameDict <: Abstractbrowser.HLIDict end
abstract type AbstractNoStackAvailableItem <: AbstractHierListItem end
abstract type AbstractHierStackRoot <: AbstractHierListItem end
abstract type AbstractHierListDebugger <: Abstracthierlist.HierListWithItems end
abstract type AbstractDebuggerWindow <: Abstractwindow.Wnd end
abstract type AbstractDebuggerStackWindow <: AbstractDebuggerWindow end
abstract type AbstractDebuggerListViewWindow <: AbstractDebuggerWindow end
abstract type AbstractDebuggerBreakpointsWindow <: AbstractDebuggerListViewWindow end
abstract type AbstractDebuggerWatchWindow <: AbstractDebuggerListViewWindow end
abstract type AbstractDebugger <: Abstractdebugger_parent end
function _LineStateToMarker(ls)
    if ls == LINESTATE_CURRENT
        return MARKER_CURRENT
    end
    return MARKER_BREAKPOINT
end

mutable struct HierListItem <: AbstractHierListItem
end

mutable struct HierFrameItem <: AbstractHierFrameItem
    debugger
    myobject

    HierFrameItem(frame, debugger) = begin
        HierListItem(frame, repr(frame))
        new(frame, debugger)
    end
end
function GetText(self::HierFrameItem)
    name = self.myobject.f_code.co_name
    if !(name) || name == "?"
        if "__name__" in self.myobject.f_locals
            name = string(self.myobject.f_locals["__name__"]) * " module"
        else
            name = "<Debugger Context>"
        end
    end
    return "%s   (%s:%d)" % (
        name,
        split(os.path, self.myobject.f_code.co_filename)[2],
        self.myobject.f_lineno,
    )
end

function GetBitmapColumn(self::HierFrameItem)::Int64
    if self.debugger.curframe == self.myobject
        return 7
    else
        return 8
    end
end

function GetSubList(self::HierFrameItem)::Vector
    ret = []
    push!(ret, HierFrameDict(self.myobject.f_locals, "Locals", 2))
    push!(ret, HierFrameDict(self.myobject.f_globals, "Globals", 1))
    return ret
end

function IsExpandable(self::HierFrameItem)::Int64
    return 1
end

function TakeDefaultAction(self::HierFrameItem)::Int64
    set_cur_frame(self.debugger, self.myobject)
    return 1
end

mutable struct HierFrameDict <: AbstractHierFrameDict
    bitmapColumn

    HierFrameDict(dict, name, bitmapColumn) = begin
        browser.HLIDict.__init__(self, dict, name)
        new(dict, name, bitmapColumn)
    end
end
function GetBitmapColumn(self::HierFrameDict)
    return self.bitmapColumn
end

mutable struct NoStackAvailableItem <: AbstractNoStackAvailableItem
    name

    NoStackAvailableItem(why) = begin
        HierListItem(nothing, why)
        new(why)
    end
end
function IsExpandable(self::NoStackAvailableItem)::Int64
    return 0
end

function GetText(self::NoStackAvailableItem)
    return self.name
end

function GetBitmapColumn(self::NoStackAvailableItem)::Int64
    return 8
end

mutable struct HierStackRoot <: AbstractHierStackRoot
    last_stack::Vector

    HierStackRoot(debugger) = begin
        HierListItem(debugger, nothing)
        new(debugger)
    end
end
function GetSubList(self::HierStackRoot)::Vector
    debugger = self.myobject
    ret = []
    if debugger.debuggerState == DBGSTATE_BREAK
        stackUse = debugger.stack[begin:end]
        reverse(stackUse)
        self.last_stack = []
        for (frame, lineno) in stackUse
            append(self.last_stack, (frame, lineno))
            if frame == debugger.userbotframe
                break
            end
        end
    end
    for (frame, lineno) in self.last_stack
        push!(ret, HierFrameItem(frame, debugger))
    end
    return ret
end

function GetText(self::HierStackRoot)::String
    return "root item"
end

function IsExpandable(self::HierStackRoot)::Int64
    return 1
end

mutable struct HierListDebugger <: AbstractHierListDebugger
    #= Hier List of stack frames, breakpoints, whatever =#

    HierListDebugger() = begin
        hierlist.HierListWithItems.__init__(
            self,
            nothing,
            win32ui.IDB_DEBUGGER_HIER,
            nothing,
            win32api.RGB(255, 0, 0),
        )
        new()
    end
end
function Setup(self::HierListDebugger, debugger)
    root = HierStackRoot(debugger)
    AcceptRoot(self, root)
end

mutable struct DebuggerWindow <: AbstractDebuggerWindow
    debugger
    title

    DebuggerWindow(ob) = begin
        window.Wnd.__init__(self, ob)
        new(ob)
    end
end
function Init(self::DebuggerWindow, debugger)
    self.debugger = debugger
end

function GetDefRect(self::DebuggerWindow)
    defRect = LoadWindowSize(app, "Debugger Windows\\" + self.title)
    if (defRect[3] - defRect[1]) == 0
        defRect = (0, 0, 150, 150)
    end
    return defRect
end

function OnDestroy(self::DebuggerWindow, msg)
    newSize = GetWindowPlacement(self)[5]
    SaveWindowSize(
        win32com_.gen_py.framework.app,
        "Debugger Windows\\" + self.title,
        newSize,
    )
    return OnDestroy(window.Wnd, self)
end

function OnKeyDown(self::DebuggerWindow, msg)::Int64
    key = msg[3]
    if key in [13, 27, 32]
        return 1
    end
    if key in [46, 8]
        DeleteSelected(self)
        return 0
    end
    view = GetActiveView(scriptutils)
    try
        firer = view.bindings.fire_key_event
    catch exn
        if exn isa AttributeError
            firer = nothing
        end
    end
    if firer != nothing
        return firer(msg)
    else
        return 1
    end
end

function DeleteSelected(self::DebuggerWindow)
    MessageBeep(win32api)
end

function EditSelected(self::DebuggerWindow)
    MessageBeep(win32api)
end

mutable struct DebuggerStackWindow <: AbstractDebuggerStackWindow
    OnKeyDown
    debugger
    list::AbstractHierListDebugger
    listOK::Int64
    title::String

    DebuggerStackWindow(title::String = "Stack") = begin
        DebuggerWindow(win32ui.CreateTreeCtrl())
        new(title)
    end
end
function SaveState(self::DebuggerStackWindow)
    DeleteAllItems(self.list)
    self.listOK = 0
    WriteProfileVal(
        win32ui,
        "Debugger Windows\\" + self.title,
        "Visible",
        IsWindowVisible(self),
    )
end

function CreateWindow(self::DebuggerStackWindow, parent)
    style =
        (
            (
                ((win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.WS_BORDER) |
                commctrl.TVS_HASLINES
            ) | commctrl.TVS_LINESATROOT
        ) | commctrl.TVS_HASBUTTONS
    CreateWindow(self._obj_, style)
    HookMessage(self, self.OnKeyDown, win32con.WM_KEYDOWN)
    HookMessage(self, self.OnKeyDown, win32con.WM_SYSKEYDOWN)
    HierInit(self.list, parent, self)
    self.listOK = 0
end

function RespondDebuggerState(self::DebuggerStackWindow, state)
    @assert(self.debugger != nothing)
    if !(self.listOK) != 0
        self.listOK = 1
        Setup(self.list, self.debugger)
    else
        Refresh(self.list)
    end
end

function RespondDebuggerData(self::DebuggerStackWindow)
    try
        handle = GetChildItem(self, 0)
    catch exn
        if exn isa win32ui.error
            return
        end
    end
    while true
        item = ItemFromHandle(self.list, handle)
        col = GetBitmapColumn(self.list, item)
        selCol = GetSelectedBitmapColumn(self.list, item)
        if selCol === nothing
            selCol = col
        end
        if GetItemImage(self.list, handle) != (col, selCol)
            SetItemImage(self.list, handle, col, selCol)
        end
        try
            handle = GetNextSiblingItem(self, handle)
        catch exn
            if exn isa win32ui.error
                break
            end
        end
    end
end

mutable struct DebuggerListViewWindow <: AbstractDebuggerListViewWindow
    OnKeyDown
    columns
    OnListEndLabelEdit
    OnItemRightClick
    OnItemDoubleClick
    OnEditItem
    OnDeleteItem

    DebuggerListViewWindow() = begin
        DebuggerWindow(win32ui.CreateListCtrl())
        new()
    end
end
function CreateWindow(self::DebuggerListViewWindow, parent)
    list = self
    style =
        (
            ((win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.WS_BORDER) |
            commctrl.LVS_EDITLABELS
        ) | commctrl.LVS_REPORT
    CreateWindow(self._obj_, style)
    HookMessage(self, self.OnKeyDown, win32con.WM_KEYDOWN)
    HookMessage(self, self.OnKeyDown, win32con.WM_SYSKEYDOWN)
    list = self
    title, width = self.columns[1]
    itemDetails = (commctrl.LVCFMT_LEFT, width, title, 0)
    InsertColumn(list, 0, itemDetails)
    col = 1
    for (title, width) in self.columns[2:end]
        col = col + 1
        itemDetails = (commctrl.LVCFMT_LEFT, width, title, 0)
        InsertColumn(list, col, itemDetails)
    end
    HookNotify(parent, self.OnListEndLabelEdit, LVN_ENDLABELEDIT)
    HookNotify(parent, self.OnItemRightClick, commctrl.NM_RCLICK)
    HookNotify(parent, self.OnItemDoubleClick, commctrl.NM_DBLCLK)
end

function RespondDebuggerData(self::DebuggerListViewWindow)
    #= pass =#
end

function RespondDebuggerState(self::DebuggerListViewWindow, state)
    #= pass =#
end

function EditSelected(self::DebuggerListViewWindow)
    try
        sel = GetNextItem(self, -1, commctrl.LVNI_SELECTED)
    catch exn
        if exn isa win32ui.error
            return
        end
    end
    EditLabel(self, sel)
end

function OnKeyDown(self::DebuggerListViewWindow, msg)::Int64
    key = msg[3]
    if chr(key) in string.ascii_uppercase
        EditSelected(self)
        return 0
    end
    return OnKeyDown(DebuggerWindow, self)
end

function OnItemDoubleClick(self::DebuggerListViewWindow, notify_data, extra)
    EditSelected(self)
end

function OnItemRightClick(self::DebuggerListViewWindow, notify_data, extra)
    pt = ScreenToClient(self, GetCursorPos(win32api))
    flags, hItem, subitem = HitTest(self, pt)
    if hItem == -1 || (commctrl.TVHT_ONITEM & flags) == 0
        return nothing
    end
    SetItemState(self, hItem, commctrl.LVIS_SELECTED, commctrl.LVIS_SELECTED)
    menu = CreatePopupMenu(win32ui)
    AppendMenu(menu, win32con.MF_STRING | win32con.MF_ENABLED, 1000, "Edit item")
    AppendMenu(menu, win32con.MF_STRING | win32con.MF_ENABLED, 1001, "Delete item")
    dockbar = GetParent(self)
    if IsFloating(dockbar)
        hook_parent = GetMainFrame(win32ui)
    else
        hook_parent = GetParentFrame(self)
    end
    HookCommand(hook_parent, self.OnEditItem, 1000)
    HookCommand(hook_parent, self.OnDeleteItem, 1001)
    TrackPopupMenu(menu, GetCursorPos(win32api))
    return nothing
end

function OnDeleteItem(self::DebuggerListViewWindow, command, code)
    DeleteSelected(self)
end

function OnEditItem(self::DebuggerListViewWindow, command, code)
    EditSelected(self)
end

mutable struct DebuggerBreakpointsWindow <: AbstractDebuggerBreakpointsWindow
    columns::Vector{Tuple}
    title::String

    DebuggerBreakpointsWindow(
        columns::Vector{Tuple} = [("Condition", 70), ("Location", 1024)],
        title::String = "Breakpoints",
    ) = new(columns, title)
end
function SaveState(self::DebuggerBreakpointsWindow)::Int64
    items = []
    for i = 0:GetItemCount(self)-1
        push!(items, GetItemText(self, i, 0))
        push!(items, GetItemText(self, i, 1))
    end
    WriteProfileVal(
        win32ui,
        "Debugger Windows\\" + self.title,
        "BreakpointList",
        join(items, "\t"),
    )
    WriteProfileVal(
        win32ui,
        "Debugger Windows\\" + self.title,
        "Visible",
        IsWindowVisible(self),
    )
    return 1
end

function OnListEndLabelEdit(self::DebuggerBreakpointsWindow, std, extra)
    item = extra[1]
    text = item[5]
    if text === nothing
        return
    end
    item_id = GetItem(self, item[1])[7]
    for bplist in values(Breakpoint.bplist)
        for bp in bplist
            if id(bp) == item_id
                if lower(strip(text)) == "none"
                    text = nothing
                end
                bp.cond = text
                break
            end
        end
    end
    RespondDebuggerData(self)
end

function DeleteSelected(self::DebuggerBreakpointsWindow)
    try
        num = GetNextItem(self, -1, commctrl.LVNI_SELECTED)
        item_id = GetItem(self, num)[7]
        for bplist in collect(values(Breakpoint.bplist))
            for bp in bplist
                if id(bp) == item_id
                    clear_break(self.debugger, bp.file, bp.line)
                    break
                end
            end
        end
    catch exn
        if exn isa win32ui.error
            MessageBeep(win32api)
        end
    end
    RespondDebuggerData(self)
end

function RespondDebuggerData(self::DebuggerBreakpointsWindow)
    l = self
    DeleteAllItems(l)
    index = -1
    for bplist in values(Breakpoint.bplist)
        for bp in bplist
            baseName = split(os.path, bp.file)[2]
            cond = bp.cond
            item = (index + 1, 0, 0, 0, string(cond), 0, id(bp))
            index = InsertItem(l, item)
            SetItemText(l, index, 1, "%s: %s" % (baseName, bp.line))
        end
    end
end

mutable struct DebuggerWatchWindow <: AbstractDebuggerWatchWindow
    debugger
    columns::Vector{Tuple}
    title::String

    DebuggerWatchWindow(
        debugger,
        columns::Vector{Tuple} = [("Expression", 70), ("Value", 1024)],
        title::String = "Watch",
    ) = new(debugger, columns, title)
end
function CreateWindow(self::DebuggerWatchWindow, parent)
    CreateWindow(DebuggerListViewWindow, self)
    items =
        split(GetProfileVal(win32ui, "Debugger Windows\\" + self.title, "Items", ""), "\t")
    index = -1
    for item in items
        if item
            index = InsertItem(self, index + 1, item)
        end
    end
    InsertItem(self, index + 1, "<New Item>")
end

function SaveState(self::DebuggerWatchWindow)::Int64
    items = []
    for i = 0:GetItemCount(self)-1-1
        push!(items, GetItemText(self, i, 0))
    end
    WriteProfileVal(win32ui, "Debugger Windows\\" + self.title, "Items", join(items, "\t"))
    WriteProfileVal(
        win32ui,
        "Debugger Windows\\" + self.title,
        "Visible",
        IsWindowVisible(self),
    )
    return 1
end

function OnListEndLabelEdit(self::DebuggerWatchWindow, std, extra)
    item = extra[1]
    itemno = item[1]
    text = item[5]
    if text === nothing
        return
    end
    SetItemText(self, itemno, 0, text)
    if itemno == (GetItemCount(self) - 1)
        InsertItem(self, itemno + 1, "<New Item>")
    end
    RespondDebuggerState(self, self.debugger.debuggerState)
end

function DeleteSelected(self::DebuggerWatchWindow)
    try
        num = GetNextItem(self, -1, commctrl.LVNI_SELECTED)
        if num < (GetItemCount(self) - 1)
            DeleteItem(self, num)
        end
    catch exn
        if exn isa win32ui.error
            MessageBeep(win32api)
        end
    end
end

function RespondDebuggerState(self::DebuggerWatchWindow, state)
    globs = nothing
    locs = nothing
    if state == DBGSTATE_BREAK
        if self.debugger.curframe
            globs = self.debugger.curframe.f_globals
            locs = self.debugger.curframe.f_locals
        end
    elseif state == DBGSTATE_NOT_DEBUGGING
        globs = __main__.__dict__
        locs = __main__.__dict__
    end
    for i = 0:GetItemCount(self)-1-1
        text = GetItemText(self, i, 0)
        if globs === nothing
            val = ""
        else
            try
                val = repr(eval(text, globs, locs))
            catch exn
                if exn isa SyntaxError
                    val = "Syntax Error"
                end
                t, v, tb = exc_info(sys)
                val = strip(format_exception_only(traceback, t, v)[1])
                tb = nothing
            end
        end
        SetItemText(self, i, 1, val)
    end
end

function CreateDebuggerDialog(parent, klass)
    control = klass()
    CreateWindow(control, parent)
    return control
end

DebuggerDialogInfos = (
    (59408, DebuggerStackWindow, nothing),
    (59409, DebuggerBreakpointsWindow, (10, 10)),
    (59410, DebuggerWatchWindow, nothing),
)
function PrepareControlBars(frame)
    style =
        (
            ((win32con.WS_CHILD | afxres.CBRS_SIZE_DYNAMIC) | afxres.CBRS_TOP) |
            afxres.CBRS_TOOLTIPS
        ) | afxres.CBRS_FLYBY
    tbd = CreateToolBar(win32ui, frame, style, win32ui.ID_VIEW_TOOLBAR_DBG)
    ModifyStyle(tbd, 0, commctrl.TBSTYLE_FLAT)
    LoadToolBar(tbd, win32ui.IDR_DEBUGGER)
    EnableDocking(tbd, afxres.CBRS_ALIGN_ANY)
    SetWindowText(tbd, "Debugger")
    DockControlBar(frame, tbd)
    for (id, klass, float) in DebuggerDialogInfos
        try
            GetControlBar(frame, id)
            exists = 1
        catch exn
            if exn isa win32ui.error
                exists = 0
            end
        end
        if exists != 0
            continue
        end
        bar = DockingBar(win32com_.gen_py.docking.DockingBar)
        style = win32con.WS_CHILD | afxres.CBRS_LEFT
        CreateWindow(
            bar,
            frame,
            CreateDebuggerDialog,
            klass.title,
            id,
            style,
            childCreatorArgs = (klass,),
        )
        SetBarStyle(
            bar,
            ((GetBarStyle(bar) | afxres.CBRS_TOOLTIPS) | afxres.CBRS_FLYBY) |
            afxres.CBRS_SIZE_DYNAMIC,
        )
        EnableDocking(bar, afxres.CBRS_ALIGN_ANY)
        if float === nothing
            DockControlBar(frame, bar)
        else
            FloatControlBar(frame, bar, float, afxres.CBRS_ALIGN_ANY)
        end
    end
end

SKIP_NONE = 0
SKIP_STEP = 1
SKIP_RUN = 2
debugger_parent = pdb.Pdb
mutable struct Debugger <: AbstractDebugger
    inited::Int64
    skipBotFrame::Int64
    userbotframe
    frameShutdown::Int64
    pumping::Int64
    debuggerState
    shownLineCurrent
    shownLineCallstack
    last_cmd_debugged::String
    abortClosed::Int64
    isInitialBreakpoint::Int64
    inForcedGUI
    options
    bAtException::Int64
    bAtPostMortem::Int64
    quitting::Int64
    botframe
    curframe
    curindex
    bFrameEnabled
    oldForeground
    oldFrameEnableState
    trace_dispatch
    stack

    Debugger() = begin
        debugger_parent.__init__(self)
        for doc in editor.editorTemplate.GetDocumentList()
            lineNo = -1
            while 1
                lineNo = doc.MarkerGetNext(lineNo + 1, MARKER_BREAKPOINT)
                if lineNo <= 0
                    break
                end
                set_break(doc.GetPathName(), lineNo)
            end
        end
        reset()
        new()
    end
end
function __del__(self::Debugger)
    close(self)
end

function close(self::Debugger, frameShutdown = 0)::Int64
    if self.pumping != 0
        if !StopDebuggerPump(self)
            return 0
        end
    end
    self.frameShutdown = frameShutdown
    if !(self.inited) != 0
        return 1
    end
    self.inited = 0
    SetInteractiveContext(nothing, nothing)
    frame = GetMainFrame(win32ui)
    for (id, klass, float) in DebuggerDialogInfos
        try
            tb = GetControlBar(frame, id)
            if tb.dialog != nothing
                SaveState(tb.dialog)
                ShowControlBar(frame, tb, 0, 1)
            end
        catch exn
            if exn isa win32ui.error
                #= pass =#
            end
        end
    end
    _UnshowCurrentLine(self)
    set_quit(self)
    return 1
end

function StopDebuggerPump(self::Debugger)::Int64
    @assert(self.pumping)
    if GUIAboutToFinishInteract(self)
        self.pumping = 0
        StopDebuggerPump(win32ui)
        return 1
    end
    return 0
end

function get_option(self::Debugger, option)
    #= Public interface into debugger options =#
    try
        return self.options[option+1]
    catch exn
        if exn isa KeyError
            throw(error("Option %s is not a valid option" % option))
        end
    end
end

function prep_run(self::Debugger, cmd)
    #= pass =#
end

function done_run(self::Debugger, cmd = nothing)
    RespondDebuggerState(self, DBGSTATE_NOT_DEBUGGING)
    close(self)
end

function canonic(self::Debugger, fname)
    return lower(abspath(os.path, fname))
end

function reset(self::Debugger)
    reset(debugger_parent)
    self.userbotframe = nothing
    UpdateAllLineStates(self)
    _UnshowCurrentLine(self)
end

function setup(self::Debugger, f, t)
    setup(debugger_parent, self, f)
    self.bAtException = t != nothing
end

function set_break(self::Debugger, filename, lineno, temporary = 0, cond = nothing)
    filename = canonic(self, filename)
    SetLineState(self, filename, lineno, LINESTATE_BREAKPOINT)
    return set_break(debugger_parent, self, filename, lineno, temporary)
end

function clear_break(self::Debugger, filename, lineno)
    filename = canonic(self, filename)
    ResetLineState(self, filename, lineno, LINESTATE_BREAKPOINT)
    return clear_break(debugger_parent, self, filename)
end

function cmdloop(self::Debugger)
    if self.frameShutdown != 0
        return
    end
    GUIAboutToBreak(self)
end

function print_stack_entry(self::Debugger, frame)
    #= pass =#
end

function user_return(self::Debugger, frame, return_value)
    frame.f_locals["__return__"] = return_value
    interaction(self, frame, nothing)
end

function user_call(self::Debugger, frame, args)
    if stop_here(self, frame)
        interaction(self, frame, nothing)
    end
end

function user_exception(self::Debugger, frame, exc_info)
    exc_type, exc_value, exc_traceback = exc_info
    if get_option(self, OPT_STOP_EXCEPTIONS)
        frame.f_locals["__exception__"] = (exc_type, exc_value)
        println("Unhandled exception while debugging...")
        if sys.version_info > (3,) && !isa(exc_value, BaseException)
            if !isa(exc_value, tuple)
                exc_value = (exc_value,)
            end
            exc_value = exc_type(exc_value...)
        end
        print_exception(traceback, exc_type, exc_value, exc_traceback)
        interaction(self, frame, exc_traceback)
    end
end

function user_line(self::Debugger, frame)
    if frame.f_lineno == 0
        return
    end
    user_line(debugger_parent, self)
end

function stop_here(self::Debugger, frame)::Int64
    if self.isInitialBreakpoint != 0
        self.isInitialBreakpoint = 0
        set_continue(self)
        return 0
    end
    if frame == self.botframe && self.skipBotFrame == SKIP_RUN
        set_continue(self)
        return 0
    end
    if frame == self.botframe && self.skipBotFrame == SKIP_STEP
        set_step(self)
        return 0
    end
    return stop_here(debugger_parent, self)
end

function run(self::Debugger, cmd, globals = nothing, locals = nothing, start_stepping = 1)
    if !isa(cmd, (str, types.CodeType))
        throw(TypeError("Only strings can be run"))
    end
    self.last_cmd_debugged = cmd
    if start_stepping
        self.isInitialBreakpoint = 0
    else
        self.isInitialBreakpoint = 1
    end
    try
        if globals === nothing
            globals = __main__.__dict__
        end
        if locals === nothing
            locals = globals
        end
        reset(self)
        prep_run(self, cmd)
        settrace(sys, self.trace_dispatch)
        if type_(cmd) != types.CodeType
            cmd = cmd * "\n"
        end
        try
            try
                if start_stepping
                    self.skipBotFrame = SKIP_STEP
                else
                    self.skipBotFrame = SKIP_RUN
                end
                exec(cmd, globals, locals)
            catch exn
                if exn isa bdb.BdbQuit
                    #= pass =#
                end
            end
        finally
            self.skipBotFrame = SKIP_NONE
            self.quitting = 1
            settrace(sys, nothing)
        end
    finally
        done_run(self, cmd)
    end
end

function runeval(self::Debugger, expr, globals = nothing, locals = nothing)
    prep_run(self, expr)
    try
        runeval(debugger_parent, self, expr, globals)
    finally
        done_run(self, expr)
    end
end

function runexec(self::Debugger, what, globs = nothing, locs = nothing)
    reset(self)
    settrace(sys, self.trace_dispatch)
    try
        try
            exec(what, globs, locs)
        catch exn
            if exn isa bdb.BdbQuit
                #= pass =#
            end
        end
    finally
        self.quitting = 1
        settrace(sys, nothing)
    end
end

function do_set_step(self::Debugger)
    if GUIAboutToRun(self)
        set_step(self)
    end
end

function do_set_next(self::Debugger)
    if GUIAboutToRun(self)
        set_next(self, self.curframe)
    end
end

function do_set_return(self::Debugger)
    if GUIAboutToRun(self)
        set_return(self, self.curframe)
    end
end

function do_set_continue(self::Debugger)
    if GUIAboutToRun(self)
        set_continue(self)
    end
end

function set_quit(self::Debugger)
    ok = 1
    if self.pumping != 0
        ok = StopDebuggerPump(self)
    end
    if ok != 0
        set_quit(debugger_parent)
    end
end

function _dump_frame_(self::Debugger, frame, name = nothing)
    if name === nothing
        name = ""
    end
    if frame
        if frame.f_code && frame.f_code.co_filename
            fname = split(os.path, frame.f_code.co_filename)[2]
        else
            fname = "??"
        end
        println(repr(name), fname, frame.f_lineno, frame)
    else
        println(repr(name), "None")
    end
end

function set_trace(self::Debugger)
    try
        1 + ""
    catch exn
        frame = exc_info(sys)[3].tb_frame.f_back.f_back
    end
    reset(self)
    self.userbotframe = nothing
    while frame
        if "_debugger_stop_frame_" in frame.f_locals
            self.userbotframe = frame
            break
        end
        frame.f_trace = self.trace_dispatch
        self.botframe = frame
        frame = frame.f_back
    end
    set_step(self)
    settrace(sys, self.trace_dispatch)
end

function set_cur_frame(self::Debugger, frame)
    @assert(frame != nothing)
    self.curframe = frame
    for (f, index) in self.stack
        if f == frame
            self.curindex = index
            break
        end
    end
    SetInteractiveContext(frame.f_globals, frame.f_locals)
    GUIRespondDebuggerData(self)
    ShowCurrentLine(self)
end

function IsBreak(self::Debugger)::Bool
    return self.debuggerState == DBGSTATE_BREAK
end

function IsDebugging(self::Debugger)::Bool
    return self.debuggerState != DBGSTATE_NOT_DEBUGGING
end

function RespondDebuggerState(self::Debugger, state)
    if state == self.debuggerState
        return
    end
    if state == DBGSTATE_NOT_DEBUGGING
        title = ""
    elseif state == DBGSTATE_RUNNING
        title = " - running"
    elseif state == DBGSTATE_BREAK
        if self.bAtException != 0
            if self.bAtPostMortem != 0
                title = " - post mortem exception"
            else
                title = " - exception"
            end
        else
            title = " - break"
        end
    else
        throw(error("Invalid debugger state passed!"))
    end
    SetWindowText(GetMainFrame(win32ui), LoadString(win32ui, win32ui.IDR_MAINFRAME) + title)
    if self.debuggerState == DBGSTATE_QUITTING && state != DBGSTATE_NOT_DEBUGGING
        println("Ignoring state change cos Im trying to stop!", state)
        return
    end
    self.debuggerState = state
    try
        frame = GetMainFrame(win32ui)
    catch exn
        if exn isa win32ui.error
            frame = nothing
        end
    end
    if frame != nothing
        for (id, klass, float) in DebuggerDialogInfos
            cb = GetControlBar(GetMainFrame(win32ui), id).dialog
            RespondDebuggerState(cb, state)
        end
    end
    for doc in GetDocumentList(editor.editorTemplate)
        OnDebuggerStateChange(doc, state)
    end
    ShowCurrentLine(self)
end

function GUICheckInit(self::Debugger)
    if self.inited != 0
        return
    end
    self.inited = 1
    frame = GetMainFrame(win32ui)
    for (id, klass, float) in DebuggerDialogInfos
        w = GetControlBar(frame, id)
        Init(w.dialog, self)
        if GetProfileVal(win32ui, "Debugger Windows\\" + w.dialog.title, "Visible", 0)
            ShowControlBar(frame, w, 1, 1)
        end
    end
    tb = GetControlBar(frame, win32ui.ID_VIEW_TOOLBAR_DBG)
    ShowControlBar(frame, tb, 1, 1)
    GUIRespondDebuggerData(self)
end

function GetDebuggerBar(self::Debugger, barName)
    frame = GetMainFrame(win32ui)
    for (id, klass, float) in DebuggerDialogInfos
        if klass.title == barName
            return GetControlBar(frame, id)
        end
    end
    @assert(0)
end

function GUIRespondDebuggerData(self::Debugger)
    if !(self.inited) != 0
        return
    end
    for (id, klass, float) in DebuggerDialogInfos
        cb = GetControlBar(GetMainFrame(win32ui), id).dialog
        RespondDebuggerData(cb)
    end
end

function GUIAboutToRun(self::Debugger)::Int64
    if !StopDebuggerPump(self) != 0
        return 0
    end
    _UnshowCurrentLine(self)
    RespondDebuggerState(self, DBGSTATE_RUNNING)
    SetInteractiveContext(nothing, nothing)
    return 1
end

function GUIAboutToBreak(self::Debugger)
    #= Called as the GUI debugger is about to get context, and take control of the running program. =#
    GUICheckInit(self)
    RespondDebuggerState(self, DBGSTATE_BREAK)
    GUIAboutToInteract(self)
    if self.pumping != 0
        println("!!! Already pumping - outa here")
        return
    end
    self.pumping = 1
    StartDebuggerPump(win32ui)
    @assert(!(self.pumping))
    if self.frameShutdown != 0
        PostMessage(GetMainFrame(win32ui), win32con.WM_CLOSE)
    end
end

function GUIAboutToInteract(self::Debugger)
    #= Called as the GUI is about to perform any interaction with the user =#
    frame = GetMainFrame(win32ui)
    self.bFrameEnabled = IsWindowEnabled(frame)
    self.oldForeground = nothing
    fw = GetForegroundWindow(win32ui)
    if fw != frame
        self.oldForeground = fw
        self.oldFrameEnableState = IsWindowEnabled(frame)
        EnableWindow(frame, 1)
    end
    if self.inForcedGUI && !IsWindowVisible(frame)
        ShowWindow(frame, win32con.SW_SHOW)
        UpdateWindow(frame)
    end
    if self.curframe
        SetInteractiveContext(self.curframe.f_globals, self.curframe.f_locals)
    else
        SetInteractiveContext(nothing, nothing)
    end
    GUIRespondDebuggerData(self)
end

function GUIAboutToFinishInteract(self::Debugger)::Int64
    #= Called as the GUI is about to finish any interaction with the user
            Returns non zero if we are allowed to stop interacting =#
    if self.oldForeground != nothing
        try
            EnableWindow(GetMainFrame(win32ui), self.oldFrameEnableState)
            EnableWindow(self.oldForeground, 1)
        catch exn
            if exn isa win32ui.error
                #= pass =#
            end
        end
    end
    if !(self.inForcedGUI)
        return 1
    end
    for template in GetDocTemplateList(GetApp(win32ui))
        for doc in GetDocumentList(template)
            if !SaveModified(doc)
                return 0
            end
        end
    end
    if get_option(self, OPT_HIDE)
        frame = GetMainFrame(win32ui)
        ShowWindow(frame, win32con.SW_HIDE)
    end
    return 1
end

function ShowLineState(self::Debugger, fileName, lineNo, lineState)
    ShowLineNo(self, fileName, lineNo)
    SetLineState(self, fileName, lineNo, lineState)
end

function SetLineState(self::Debugger, fileName, lineNo, lineState)
    doc = FindOpenDocument(editor.editorTemplate, fileName)
    if doc != nothing
        marker = _LineStateToMarker(lineState)
        if !MarkerCheck(doc, lineNo, marker)
            MarkerAdd(doc, lineNo, marker)
        end
    end
end

function ResetLineState(self::Debugger, fileName, lineNo, lineState)
    doc = FindOpenDocument(editor.editorTemplate, fileName)
    if doc != nothing
        marker = _LineStateToMarker(lineState)
        MarkerDelete(doc, lineNo, marker)
    end
end

function UpdateDocumentLineStates(self::Debugger, doc)
    MarkerDeleteAll(doc, MARKER_BREAKPOINT)
    MarkerDeleteAll(doc, MARKER_CURRENT)
    fname = canonic(self, GetPathName(doc))
    for line in get(self.breaks, fname, [])
        MarkerAdd(doc, line, MARKER_BREAKPOINT)
    end
    if self.shownLineCurrent && fname == self.shownLineCurrent[1]
        lineNo = self.shownLineCurrent[2]
        if !MarkerCheck(doc, lineNo, MARKER_CURRENT)
            MarkerAdd(doc, lineNo, MARKER_CURRENT)
        end
    end
end

function UpdateAllLineStates(self::Debugger)
    for doc in GetDocumentList(editor.editorTemplate)
        UpdateDocumentLineStates(self, doc)
    end
end

function ShowCurrentLine(self::Debugger)
    _UnshowCurrentLine(self)
    if self.curframe
        fileName = canonic(self, self.curframe.f_code.co_filename)
        lineNo = self.curframe.f_lineno
        self.shownLineCurrent = (fileName, lineNo)
        ShowLineState(self, fileName, lineNo, LINESTATE_CURRENT)
    end
end

function _UnshowCurrentLine(self::Debugger)
    #= Unshow the current line, and forget it =#
    if self.shownLineCurrent != nothing
        fname, lineno = self.shownLineCurrent
        ResetLineState(self, fname, lineno, LINESTATE_CURRENT)
        self.shownLineCurrent = nothing
    end
end

function ShowLineNo(self::Debugger, filename, lineno)::Int64
    wasOpen = FindOpenDocument(editor.editorTemplate, filename) != nothing
    if isfile(os.path, filename) && JumpToDocument(scriptutils, filename, lineno)
        if !(wasOpen)
            doc = FindOpenDocument(editor.editorTemplate, filename)
            if doc != nothing
                UpdateDocumentLineStates(self, doc)
                return 1
            end
            return 0
        end
        return 1
    else
        line = getline(linecache, filename, lineno)
        @printf(
            "%s(%d): %s",
            (basename(os.path, filename), lineno, expandtabs(line[begin:-1], 4))
        )
        return 0
    end
end

end
