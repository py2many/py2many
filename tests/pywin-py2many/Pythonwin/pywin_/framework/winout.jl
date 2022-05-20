using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
include("scriptutils.jl")
include("help.jl")
import _thread
import string
using win32com_.gen_py.mfc: docview
using win32com_.gen_py.framework: app, window
import win32con
import queue
debug = (msg) -> nothing
mutable struct flags <: Abstractflags
WQ_IDLE::Int64
WQ_LINE::Int64
WQ_NONE::Int64

                    flags(WQ_IDLE::Int64 = 2, WQ_LINE::Int64 = 1, WQ_NONE::Int64 = 0) =
                        new(WQ_IDLE, WQ_LINE, WQ_NONE)
end

import win32com_.gen_py.scintilla.document
using win32com_.gen_py.scintilla: scintillacon
using win32com_.gen_py: default_scintilla_encoding
abstract type Abstractflags end
abstract type AbstractWindowOutputDocument <: AbstractWindowOutputDocumentParent end
abstract type AbstractWindowOutputFrame <: Abstractwindow.MDIChildWnd end
abstract type AbstractWindowOutputViewImpl end
abstract type AbstractWindowOutputViewRTF <: Abstractdocview.RichEditView end
abstract type AbstractWindowOutputViewScintilla <: Abstractwin32com_.gen_py.scintilla.view.CScintillaView end
abstract type AbstractWindowOutput <: Abstractdocview.DocTemplate end
WindowOutputDocumentParent = win32com_.gen_py.scintilla.document.CScintillaDocument
mutable struct WindowOutputDocument <: AbstractWindowOutputDocument

end
function SaveModified(self::WindowOutputDocument)::Int64
return 1
end

function OnSaveDocument(self::WindowOutputDocument, fileName)::Int64
SetStatusText(win32ui, "Saving file...", 1)
try
SaveFile(self, fileName)
catch exn
 let details = exn
if details isa IOError
MessageBox(win32ui, "Error - could not save file\r\n\r\n%s" % details)
return 0
end
end
end
SetStatusText(win32ui, "Ready")
return 1
end

mutable struct WindowOutputFrame <: AbstractWindowOutputFrame
template
wnd

            WindowOutputFrame(wnd = nothing) = begin
                window.MDIChildWnd.__init__(self, wnd)
HookMessage(OnSizeMove, win32con.WM_SIZE)
HookMessage(OnSizeMove, win32con.WM_MOVE)
                new(wnd )
            end
end
function LoadFrame(self::WindowOutputFrame, idResource, style, wndParent, context)
self.template = context.template
return LoadFrame(self._obj_, idResource, style, wndParent, context)
end

function PreCreateWindow(self::WindowOutputFrame, cc)
cc = PreCreateWindow(self._obj_, cc)
if self.template.defSize && self.template.defSize[1] != self.template.defSize[2]
rect = RectToCreateStructRect(app, self.template.defSize)
cc = (cc[1], cc[2], cc[3], cc[4], rect, cc[6], cc[7], cc[8], cc[9])
end
return cc
end

function OnSizeMove(self::WindowOutputFrame, msg)
mdiClient = GetParent(self)
self.template.defSize = ScreenToClient(mdiClient, GetWindowRect(self))
end

function OnDestroy(self::WindowOutputFrame, message)::Int64
OnFrameDestroy(self.template, self)
return 1
end

mutable struct WindowOutputViewImpl <: AbstractWindowOutputViewImpl
patErrorMessage
template
OnRClick
end
function HookHandlers(self::WindowOutputViewImpl)
HookMessage(self, self.OnRClick, win32con.WM_RBUTTONDOWN)
end

function OnDestroy(self::WindowOutputViewImpl, msg)
OnViewDestroy(self.template, self)
end

function OnInitialUpdate(self::WindowOutputViewImpl)
RestoreKillBuffer(self)
SetSel(self, -2)
end

function GetRightMenuItems(self::WindowOutputViewImpl)::Vector
ret = []
flags = win32con.MF_STRING | win32con.MF_ENABLED
push!(ret, (flags, win32ui.ID_EDIT_COPY, "&Copy"))
push!(ret, (flags, win32ui.ID_EDIT_SELECT_ALL, "&Select all"))
return ret
end

function OnRClick(self::WindowOutputViewImpl, params)::Int64
paramsList = GetRightMenuItems(self)
menu = CreatePopupMenu(win32ui)
for appendParams in paramsList
if type_(appendParams) != type_(())
appendParams = (appendParams,)
end
AppendMenu(menu, appendParams...)
end
TrackPopupMenu(menu, params[6])
return 0
end

function HandleSpecialLine(self::WindowOutputViewImpl)::Int64
line = GetLine(self)
if line[begin:11] == "com_error: "
try
det = eval(strip(line[find(line, ":") + 2:end]))
SetStatusText(win32ui, "Opening help file on OLE error...")
OpenHelpFile(help, det[3][4], win32con.HELP_CONTEXT, det[3][5])
return 1
catch exn
 let details = exn
if details isa win32api.error
SetStatusText(win32ui, "The help file could not be opened - %s" % details.strerror)
return 1
end
end
SetStatusText(win32ui, "Line is a COM error, but no WinHelp details can be parsed")
end
end
matchResult = match(self.patErrorMessage, line)
if matchResult === nothing
lineNo = LineFromChar(self)
if lineNo > 0
line = GetLine(self, lineNo - 1)
matchResult = match(self.patErrorMessage, line)
end
end
if matchResult != nothing
fileName = group(matchResult, 1)
if fileName[1] == "<"
SetStatusText(win32ui, "Can not load this file")
return 1
else
lineNoString = group(matchResult, 2)
fileNameSpec = fileName
fileName = LocatePythonFile(scriptutils, fileName)
if fileName === nothing
SetStatusText(win32ui, "Cant locate the file \'%s\'" % fileNameSpec, 0)
return 1
end
SetStatusText(win32ui, ("Jumping to line " + lineNoString) * " of file " + fileName, 1)
if !JumpToDocument(scriptutils, fileName, parse(Int, lineNoString))
SetStatusText(win32ui, "Could not open %s" % fileName)
return 1
end
return 1
end
end
return 0
end

function write(self::WindowOutputViewImpl, msg)
return write(self.template, msg)
end

function writelines(self::WindowOutputViewImpl, lines)
for line in lines
write(self, line)
end
end

function flush(self::WindowOutputViewImpl)
flush(self.template)
end

mutable struct WindowOutputViewRTF <: docview.RichEditView
OnLDoubleClick
template
_StreamRTFIn
_StreamRTFOut

            WindowOutputViewRTF(doc) = begin
                docview.RichEditView.__init__(self, doc)
WindowOutputViewImpl()
                new(doc)
            end
end
function OnInitialUpdate(self::WindowOutputViewRTF)
OnInitialUpdate(WindowOutputViewImpl)
return OnInitialUpdate(docview.RichEditView)
end

function OnDestroy(self::WindowOutputViewRTF, msg)
OnDestroy(WindowOutputViewImpl, self)
OnDestroy(docview.RichEditView, self)
end

function HookHandlers(self::WindowOutputViewRTF)
HookHandlers(WindowOutputViewImpl)
HookMessage(self, self.OnLDoubleClick, win32con.WM_LBUTTONDBLCLK)
end

function OnLDoubleClick(self::WindowOutputViewRTF, params)::Int64
if HandleSpecialLine(self)
return 0
end
return 1
end

function RestoreKillBuffer(self::WindowOutputViewRTF)
if length(self.template.killBuffer) != 0
StreamIn(self, win32con.SF_RTF, self._StreamRTFIn)
self.template.killBuffer = []
end
end

function SaveKillBuffer(self::WindowOutputViewRTF)
StreamOut(self, win32con.SF_RTFNOOBJS, self._StreamRTFOut)
end

function _StreamRTFOut(self::WindowOutputViewRTF, data)::Int64
append(self.template.killBuffer, data)
return 1
end

function _StreamRTFIn(self::WindowOutputViewRTF, bytes)
try
item = self.template.killBuffer[1]
remove(self.template.killBuffer, item)
if bytes < length(item)
println("Warning - output buffer not big enough!")
end
return item
catch exn
if exn isa IndexError
return nothing
end
end
end

function dowrite(self::WindowOutputViewRTF, str)
SetSel(self, -2)
ReplaceSel(self, str)
end

import win32com_.gen_py.scintilla.view
mutable struct WindowOutputViewScintilla <: win32com_.gen_py.scintilla.view.CScintillaView
OnScintillaDoubleClick
template

            WindowOutputViewScintilla(doc) = begin
                win32com_.gen_py.scintilla.view.CScintillaView.__init__(self, doc)
WindowOutputViewImpl()
                new(doc)
            end
end
function OnInitialUpdate(self::WindowOutputViewScintilla)
OnInitialUpdate(win32com_.gen_py.scintilla.view.CScintillaView)
SCISetMarginWidth(self, 3)
OnInitialUpdate(WindowOutputViewImpl)
end

function OnDestroy(self::WindowOutputViewScintilla, msg)
OnDestroy(WindowOutputViewImpl, self)
OnDestroy(win32com_.gen_py.scintilla.view.CScintillaView, self)
end

function HookHandlers(self::WindowOutputViewScintilla)
HookHandlers(WindowOutputViewImpl)
HookHandlers(win32com_.gen_py.scintilla.view.CScintillaView)
HookNotify(GetParent(self), self.OnScintillaDoubleClick, scintillacon.SCN_DOUBLECLICK)
end

function OnScintillaDoubleClick(self::WindowOutputViewScintilla, std, extra)
HandleSpecialLine(self)
end

function RestoreKillBuffer(self::WindowOutputViewScintilla)
@assert(length(self.template.killBuffer) ∈ [0, 1])
if self.template.killBuffer
SCIAddText(self, self.template.killBuffer[1])
end
self.template.killBuffer = []
end

function SaveKillBuffer(self::WindowOutputViewScintilla)
self.template.killBuffer = [GetTextRange(self, 0, -1)]
end

function dowrite(self::WindowOutputViewScintilla, str)
end_ = GetTextLength(self)
atEnd = end_ == GetSel(self)[1]
SCIInsertText(self, str, end_)
if atEnd
SetSel(self, GetTextLength(self))
end
end

function SetWordWrap(self::WindowOutputViewScintilla, bWrapOn = 1)
if bWrapOn
wrap_mode = scintillacon.SC_WRAP_WORD
else
wrap_mode = scintillacon.SC_WRAP_NONE
end
SCISetWrapMode(self, wrap_mode)
end

function _MakeColorizer(self::WindowOutputViewScintilla)
return nothing
end

WindowOutputView = WindowOutputViewScintilla
mutable struct WindowOutput <: AbstractWindowOutput
#= Looks like a general Output Window - text can be written by the 'write' method.
    Will auto-create itself on first write, and also on next write after being closed =#
QueueIdleHandler
bAutoRestore
bCreating::Int64
currentView
defSize
errorCantRecreate::Int64
idleHandlerSet::Int64
iniSizeSection
interruptCount::Int64
killBuffer::Vector
loadedSize
mainThreadId
outputQueue
style
title
writeQueueing
makeDoc
makeFrame
makeView
queueing
softspace::Int64

            WindowOutput(title = nothing, defSize = nothing, queueing = flags.WQ_LINE, bAutoRestore = 1, style = nothing, makeDoc = nothing, makeFrame = nothing, makeView = nothing, softspace::Int64 = 1) = begin
                if makeDoc === nothing
makeDoc = WindowOutputDocument
end
if makeFrame === nothing
makeFrame = WindowOutputFrame
end
if makeView === nothing
makeView = WindowOutputViewScintilla
end
docview.DocTemplate.__init__(self, win32ui.IDR_PYTHONTYPE, makeDoc, makeFrame, makeView)
SetDocStrings("\nOutput\n\nText Documents (*.txt)\n.txt\n\n\n")
win32ui.GetApp().AddDocTemplate(self)
if type_(defSize) == type_("")
iniSizeSection = defSize
defSize = app.LoadWindowSize(defSize)
loadedSize = defSize
else
iniSizeSection = nothing
defSize = defSize
end
SetIdleHandler()
                new(title , defSize , queueing , bAutoRestore , style , makeDoc , makeFrame , makeView , softspace)
            end
end
function __del__(self::WindowOutput)
Close(self)
end

function Create(self::WindowOutput, title = nothing, style = nothing)
self.bCreating = 1
if title
self.title = title
end
if style
self.style = style
end
doc = OpenDocumentFile(self)
if doc === nothing
return
end
self.currentView = GetFirstView(doc)
self.bCreating = 0
if self.title
SetTitle(doc, self.title)
end
end

function Close(self::WindowOutput)
RemoveIdleHandler(self)
try
parent = GetParent(self.currentView)
catch exn
if exn isa (AttributeError, win32ui.error)
return
end
end
DestroyWindow(parent)
end

function SetTitle(self::WindowOutput, title)
self.title = title
if self.currentView
SetTitle(GetDocument(self.currentView), self.title)
end
end

function OnViewDestroy(self::WindowOutput, view)
SaveKillBuffer(self.currentView)
self.currentView = nothing
end

function OnFrameDestroy(self::WindowOutput, frame)
if self.iniSizeSection
newSize = GetWindowPlacement(frame)[5]
if self.loadedSize != newSize
SaveWindowSize(app, self.iniSizeSection, newSize)
end
end
end

function SetIdleHandler(self::WindowOutput)
if !(self.idleHandlerSet) != 0
debug("Idle handler set\n")
AddIdleHandler(GetApp(win32ui), self.QueueIdleHandler)
self.idleHandlerSet = 1
end
end

function RemoveIdleHandler(self::WindowOutput)
if self.idleHandlerSet != 0
debug("Idle handler reset\n")
if DeleteIdleHandler(GetApp(win32ui), self.QueueIdleHandler) == 0
debug("Error deleting idle handler\n")
end
self.idleHandlerSet = 0
end
end

function RecreateWindow(self::WindowOutput)::Int64
if self.errorCantRecreate != 0
debug("Error = not trying again")
return 0
end
try
GetSafeHwnd(GetMainFrame(win32ui))
Create(self)
return 1
catch exn
if exn isa (win32ui.error, AttributeError)
self.errorCantRecreate = 1
debug("Winout can not recreate the Window!\n")
return 0
end
end
end

function QueueIdleHandler(self::WindowOutput, handler, count)::Int64
try
bEmpty = QueueFlush(self, 20)
if bEmpty
self.interruptCount = 0
end
catch exn
if exn isa KeyboardInterrupt
self.interruptCount = self.interruptCount + 1
if self.interruptCount > 1
self.outputQueue = Queue(queue, -1)
println("Interrupted.")
bEmpty = 1
else
error()
end
end
end
return !(bEmpty)
end

function NeedRecreateWindow(self::WindowOutput)::Int64
try
if self.currentView != nothing && IsWindow(self.currentView)
return 0
end
catch exn
if exn isa (win32ui.error, AttributeError)
#= pass =#
end
end
return 1
end

function CheckRecreateWindow(self::WindowOutput)::Int64
if self.bCreating != 0
return 1
end
if !NeedRecreateWindow(self) != 0
return 1
end
if self.bAutoRestore
if RecreateWindow(self) != 0
return 1
end
end
return 0
end

function QueueFlush(self::WindowOutput, max = nothing)::Int64
if self.bCreating != 0
return 1
end
items = []
rc = 0
while max === nothing || max > 0
try
item = get_nowait(self.outputQueue)
push!(items, item)
catch exn
if exn isa queue.Empty
rc = 1
break;
end
end
if max != nothing
max = max - 1
end
end
if length(items) != 0
if !CheckRecreateWindow(self) != 0
debug(":Recreate failed!\n")
return 1
end
PumpWaitingMessages(win32ui)
dowrite(self.currentView, join(items, ""))
end
return rc
end

function HandleOutput(self::WindowOutput, message)
put(self.outputQueue, message)
if GetCurrentThreadId(win32api) != self.mainThreadId
#= pass =#
elseif self.writeQueueing == flags.WQ_LINE
pos = rfind(message, "\n")
if pos >= 0
QueueFlush(self)
return
end
elseif self.writeQueueing == flags.WQ_NONE
QueueFlush(self)
return
end
try
PostMessage(GetMainFrame(win32ui), win32con.WM_USER)
catch exn
if exn isa win32ui.error
OutputDebugString(win32api, message)
end
end
end

function writelines(self::WindowOutput, lines)
for line in lines
write(self, line)
end
end

function write(self::WindowOutput, message)
HandleOutput(self, message)
end

function flush(self::WindowOutput)
QueueFlush(self)
end

function HandleSpecialLine(self::WindowOutput)
HandleSpecialLine(self.currentView)
end

function RTFWindowOutput()::WindowOutput
kw["makeView"] = WindowOutputViewRTF
return WindowOutput(args..., kw)
end

function thread_test(o)
for i in 0:4
write(o, "Hi from thread %d\n" % GetCurrentThreadId(win32api))
Sleep(win32api, 100)
end
end

function test()::WindowOutput
w = WindowOutput(flags.WQ_IDLE)
write(w, "First bit of text\n")
for i in 0:4
write(w, "Hello from the main thread\n")
start_new(_thread, thread_test, (w,))
end
for i in 0:1
write(w, "Hello from the main thread\n")
Sleep(win32api, 50)
end
return w
end

if abspath(PROGRAM_FILE) == @__FILE__
test()
end