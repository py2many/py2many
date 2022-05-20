using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
using win32com_.gen_py.framework: toolmenu
using win32com_.gen_py.framework: help
using win32com_.gen_py.debugger.debugger: PrepareControlBars
include("toolmenu.jl")
import win32com_.gen_py.debugger
include("intpydde.jl")
include("interact.jl")
include("scriptutils.jl")
using win32com_.gen_py.tools: browser
using win32com_.gen_py.dialogs: ideoptions
using win32com_.gen_py.debugger: configui
using win32com_.gen_py.framework.editor: editorTemplate
include("help.jl")
import win32con


import __main__


include("app.jl")

using win32com_.gen_py.mfc: afxres, dialog
import commctrl
include("dbgcommands.jl")
lastLocateFileName = ".py"
function _SetupSharedMenu_(self::InteractivePythonApp)
sharedMenu = GetSharedMenu(self)
SetToolsMenu(toolmenu, sharedMenu)
SetHelpMenuOtherHelp(help, sharedMenu)
end

using win32com_.gen_py.mfc: docview
docview.DocTemplate._SetupSharedMenu_ = _SetupSharedMenu_
mutable struct MainFrame <: AbstractMainFrame
closing::Int64
end
function OnCreate(self::MainFrame, createStruct)::Int64
self.closing = 0
if OnCreate(app.MainFrame, self) == -1
return -1
end
style = (((win32con.WS_CHILD | afxres.CBRS_SIZE_DYNAMIC) | afxres.CBRS_TOP) | afxres.CBRS_TOOLTIPS) | afxres.CBRS_FLYBY
EnableDocking(self, afxres.CBRS_ALIGN_ANY)
tb = CreateToolBar(win32ui, self, style | win32con.WS_VISIBLE)
ModifyStyle(tb, 0, commctrl.TBSTYLE_FLAT)
LoadToolBar(tb, win32ui.IDR_MAINFRAME)
EnableDocking(tb, afxres.CBRS_ALIGN_ANY)
SetWindowText(tb, "Standard")
DockControlBar(self, tb)
PrepareControlBars(self)
menu = GetMenu(self)
SetToolsMenu(toolmenu, menu, 2)
SetHelpMenuOtherHelp(help, menu)
end

function OnClose(self::MainFrame)
try
if win32com_.gen_py.debugger.currentDebugger != nothing && win32com_.gen_py.debugger.currentDebugger.pumping
try
close(win32com_.gen_py.debugger.currentDebugger, 1)
catch exn
current_exceptions() != [] ? current_exceptions()[end] : nothing
end
return
end
catch exn
if exn isa win32ui.error
#= pass =#
end
end
self.closing = 1
SaveBarState(self, "ToolbarDefault")
SetActiveView(self, nothing)
FinalizeHelp(help)
DestroyControlBar(self, afxres.AFX_IDW_TOOLBAR)
DestroyControlBar(self, win32ui.ID_VIEW_TOOLBAR_DBG)
return OnClose(self._obj_)
end

function DestroyControlBar(self::MainFrame, id)
try
bar = GetControlBar(self, id)
catch exn
if exn isa win32ui.error
return
end
end
DestroyWindow(bar)
end

function OnCommand(self::MainFrame, wparam, lparam)::Int64
try
v = GetActiveView(self)
if OnCommand(v, wparam, lparam)
return 1
end
catch exn
if exn isa (win32ui.error, AttributeError)
#= pass =#
end
end
return OnCommand(self._obj_, wparam, lparam)
end

mutable struct InteractivePythonApp <: AbstractInteractivePythonApp
ddeServer
OnViewBrowse
OnFileImport
OnFileCheck
OnUpdateFileCheck
OnFileRun
OnFileLocate
OnInteractiveWindow
OnUpdateInteractiveWindow
OnViewOptions
OnHelpIndex
OnFileSaveAll
OnViewToolbarDbg
OnUpdateViewToolbarDbg
end
function HookCommands(self::InteractivePythonApp)
HookCommands(app.CApp)
HookCommands(DebuggerCommandHandler(dbgcommands))
HookCommand(self, self.OnViewBrowse, win32ui.ID_VIEW_BROWSE)
HookCommand(self, self.OnFileImport, win32ui.ID_FILE_IMPORT)
HookCommand(self, self.OnFileCheck, win32ui.ID_FILE_CHECK)
HookCommandUpdate(self, self.OnUpdateFileCheck, win32ui.ID_FILE_CHECK)
HookCommand(self, self.OnFileRun, win32ui.ID_FILE_RUN)
HookCommand(self, self.OnFileLocate, win32ui.ID_FILE_LOCATE)
HookCommand(self, self.OnInteractiveWindow, win32ui.ID_VIEW_INTERACTIVE)
HookCommandUpdate(self, self.OnUpdateInteractiveWindow, win32ui.ID_VIEW_INTERACTIVE)
HookCommand(self, self.OnViewOptions, win32ui.ID_VIEW_OPTIONS)
HookCommand(self, self.OnHelpIndex, afxres.ID_HELP_INDEX)
HookCommand(self, self.OnFileSaveAll, win32ui.ID_FILE_SAVE_ALL)
HookCommand(self, self.OnViewToolbarDbg, win32ui.ID_VIEW_TOOLBAR_DBG)
HookCommandUpdate(self, self.OnUpdateViewToolbarDbg, win32ui.ID_VIEW_TOOLBAR_DBG)
end

function CreateMainFrame(self::InteractivePythonApp)::MainFrame
return MainFrame()
end

function MakeExistingDDEConnection(self::InteractivePythonApp)
try
catch exn
if exn isa ImportError
return nothing
end
end
conv = CreateConversation(intpydde, self.ddeServer)
try
ConnectTo(conv, "Pythonwin", "System")
return conv
catch exn
if exn isa intpydde.error
return nothing
end
end
end

function InitDDE(self::InteractivePythonApp)::Int64
try
catch exn
if exn isa ImportError
self.ddeServer = nothing
intpydde = nothing
end
end
if intpydde != nothing
self.ddeServer = DDEServer(intpydde, self)
Create(self.ddeServer, "Pythonwin", intpydde.CBF_FAIL_SELFCONNECTIONS)
try
connection = MakeExistingDDEConnection(self)
if connection != nothing
Exec(connection, "self.Activate()")
if ProcessArgs(self, append!([PROGRAM_FILE], ARGS), connection) === nothing
return 1
end
end
catch exn
DisplayTraceback(win32ui, exc_info(sys), " - error in DDE conversation with Pythonwin")
return 1
end
end
end

function InitInstance(self::InteractivePythonApp)::Int64
if "/nodde" ∉ append!([PROGRAM_FILE], ARGS) && "/new" ∉ append!([PROGRAM_FILE], ARGS) && "-nodde" ∉ append!([PROGRAM_FILE], ARGS) && "-new" ∉ append!([PROGRAM_FILE], ARGS)
if InitDDE(self) != 0
return 1
end
else
self.ddeServer = nothing
end
SetRegistryKey(win32ui, "Python %s" % (sys.winver,))
InitInstance(app.CApp)
CreateDebuggerThread(win32ui)
EnableControlContainer(win32ui)
CreateInteractiveWindowUserPreference(interact)
LoadSystemModules(self)
LoadUserModules(self)
try
LoadBarState(self.frame, "ToolbarDefault")
catch exn
if exn isa win32ui.error
#= pass =#
end
end
try
ProcessArgs(self, append!([PROGRAM_FILE], ARGS))
catch exn
DisplayTraceback(win32ui, exc_info(sys), " - error processing command line args")
end
end

function ExitInstance(self::InteractivePythonApp)
DestroyDebuggerThread(win32ui)
try
DestroyInteractiveWindow(interact)
catch exn
#= pass =#
end
if self.ddeServer != nothing
Shutdown(self.ddeServer)
self.ddeServer = nothing
end
return ExitInstance(app.CApp)
end

function Activate(self::InteractivePythonApp)
frame = GetMainFrame(win32ui)
SetForegroundWindow(frame)
if GetWindowPlacement(frame)[2] == win32con.SW_SHOWMINIMIZED
ShowWindow(frame, win32con.SW_RESTORE)
end
end

function ProcessArgs(self::InteractivePythonApp, args, dde = nothing)
if length(args) < 1 || !(args[1])
return
end
i = 0
while i < length(args)
argType = args[i + 1]
i += 1
if startswith(argType, "-")
argType = "/" * argType[2:end]
end
if !startswith(argType, "/")
argType = lower(GetProfileVal(win32ui, "Python", "Default Arg Type", "/edit"))
i -= 1
end
par = i < length(args) && args[i + 1] || "MISSING"
if argType ∈ ["/nodde", "/new", "-nodde", "-new"]
#= pass =#
elseif startswith(argType, "/goto:")
gotoline = parse(Int, argType[length("/goto:") + 1:end])
if dde
Exec(dde, "from win32com_.gen_py.framework import scriptutils\ned = scriptutils.GetActiveEditControl()\nif ed: ed.SetSel(ed.LineIndex(%s - 1))" % gotoline)
else
ed = GetActiveEditControl(scriptutils)
if ed
SetSel(ed, LineIndex(ed, gotoline - 1))
end
end
elseif argType == "/edit"
i += 1
fname = GetFullPathName(win32api, par)
if !isfile(os.path, fname)
MessageBox(win32ui, "No such file: %s\n\nCommand Line: %s" % (fname, GetCommandLine(win32api)), "Open file for edit", win32con.MB_ICONERROR)
continue;
end
if dde
Exec(dde, "win32ui.GetApp().OpenDocumentFile(%s)" % repr(fname))
else
OpenDocumentFile(GetApp(win32ui), par)
end
elseif argType == "/rundlg"
if dde
Exec(dde, "from win32com_.gen_py.framework import scriptutils;scriptutils.RunScript(%r, %r, 1)" % (par, join(args[i + 2:end], " ")))
else
RunScript(scriptutils, par, join(args[i + 2:end], " "))
end
return
elseif argType == "/run"
if dde
Exec(dde, "from win32com_.gen_py.framework import scriptutils;scriptutils.RunScript(%r, %r, 0)" % (par, join(args[i + 2:end], " ")))
else
RunScript(scriptutils, par, join(args[i + 2:end], " "), 0)
end
return
elseif argType == "/app"
throw(RuntimeError("/app only supported for new instances of Pythonwin.exe"))
elseif argType == "/dde"
if dde != nothing
Exec(dde, par)
else
MessageBox(win32ui, "The /dde command can only be used\r\nwhen Pythonwin is already running")
end
i += 1
else
throw(ValueError("Command line argument not recognised: %s" % argType))
end
end
end

function LoadSystemModules(self::InteractivePythonApp)
DoLoadModules(self, "win32com_.gen_py.framework.editor,win32com_.gen_py.framework.stdin")
end

function LoadUserModules(self::InteractivePythonApp, moduleNames = nothing)
if moduleNames === nothing
default = "win32com_.gen_py.framework.sgrepmdi,win32com_.gen_py.framework.mdi_pychecker"
moduleNames = GetProfileVal(win32ui, "Python", "Startup Modules", default)
end
DoLoadModules(self, moduleNames)
end

function DoLoadModules(self::InteractivePythonApp, moduleNames)
if !(moduleNames)
return
end
modules = split(moduleNames, ",")
for module_ in modules
try
__import__(module_)
catch exn
current_exceptions() != [] ? current_exceptions()[end] : nothing
msg = "Startup import of user module \"%s\" failed" % module_
println(msg)
MessageBox(win32ui, msg)
end
end
end

function OnDDECommand(self::InteractivePythonApp, command)
try
exec(command + "\n")
catch exn
println("ERROR executing DDE command: $(command)")
current_exceptions() != [] ? current_exceptions()[end] : nothing
error()
end
end

function OnViewBrowse(self::InteractivePythonApp, id, code)
#= Called when ViewBrowse message is received =#
obName = GetSimpleInput(dialog, "Object", "__builtins__", "Browse Python Object")
if obName === nothing
return
end
try
Browse(browser, eval(obName, __main__.__dict__, __main__.__dict__))
catch exn
if exn isa NameError
MessageBox(win32ui, "This is no object with this name")
end
if exn isa AttributeError
MessageBox(win32ui, "The object has no attribute of that name")
end
current_exceptions() != [] ? current_exceptions()[end] : nothing
MessageBox(win32ui, "This object can not be browsed")
end
end

function OnFileImport(self::InteractivePythonApp, id, code)
#= Called when a FileImport message is received. Import the current or specified file =#
ImportFile(scriptutils)
end

function OnFileCheck(self::InteractivePythonApp, id, code)
#= Called when a FileCheck message is received. Check the current file. =#
CheckFile(scriptutils)
end

function OnUpdateFileCheck(self::InteractivePythonApp, cmdui)
Enable(cmdui, GetActiveFileName(scriptutils, 0) != nothing)
end

function OnFileRun(self::InteractivePythonApp, id, code)
#= Called when a FileRun message is received. =#
showDlg = GetKeyState(win32api, win32con.VK_SHIFT) >= 0
RunScript(scriptutils, nothing, nothing, showDlg)
end

function OnFileLocate(self::InteractivePythonApp, id, code)
global lastLocateFileName
name = GetSimpleInput(dialog, "File name", lastLocateFileName, "Locate Python File")
if name === nothing
return
end
lastLocateFileName = name
if lower(lastLocateFileName[length(lastLocateFileName) - -2:end]) == ".py"
lastLocateFileName = lastLocateFileName[begin:-3]
end
lastLocateFileName = replace(lastLocateFileName, ".", "\\")
newName = LocatePythonFile(scriptutils, lastLocateFileName)
if newName === nothing
MessageBox(win32ui, "The file \'%s\' can not be located" % lastLocateFileName)
else
OpenDocumentFile(GetApp(win32ui), newName)
end
end

function OnViewOptions(self::InteractivePythonApp, id, code)
InitRichEdit(win32ui)
sheet = PropertySheet(dialog, "Pythonwin Options")
AddPage(sheet, OptionsPropPage(ideoptions))
AddPage(sheet, ToolMenuPropPage(toolmenu))
pages = []
for template in GetDocTemplateList(self)
try
getter = template.GetPythonPropertyPages
catch exn
if exn isa AttributeError
continue;
end
end
pages = pages + getter()
end
try
catch exn
if exn isa ImportError
configui = nothing
end
end
if configui != nothing
push!(pages, DebuggerOptionsPropPage(configui))
end
for page in pages
AddPage(sheet, page)
end
if DoModal(sheet) == win32con.IDOK
SetStatusText(win32ui, "Applying configuration changes...", 1)
DoWaitCursor(win32ui, 1)
SendMessageToDescendants(GetMainFrame(win32ui), win32con.WM_WININICHANGE, 0, 0)
DoWaitCursor(win32ui, 0)
end
end

function OnInteractiveWindow(self::InteractivePythonApp, id, code)
ToggleInteractiveWindow(interact)
end

function OnUpdateInteractiveWindow(self::InteractivePythonApp, cmdui)
try
interact = sys.modules["win32com_.gen_py.framework.interact"]
state = IsInteractiveWindowVisible(interact)
catch exn
if exn isa KeyError
state = 0
end
end
Enable(cmdui)
SetCheck(cmdui, state)
end

function OnFileSaveAll(self::InteractivePythonApp, id, code)
num = 0
for doc in GetDocumentList(editorTemplate)
if IsModified(doc) && GetPathName(doc)
num = 1
num = 1
OnSaveDocument(doc, GetPathName(doc))
end
end
SetStatusText(win32ui, "%d documents saved" % num, 1)
end

function OnViewToolbarDbg(self::InteractivePythonApp, id, code)
if code == 0
return !OnBarCheck(GetMainFrame(win32ui), id)
end
end

function OnUpdateViewToolbarDbg(self::InteractivePythonApp, cmdui)
OnUpdateControlBarMenu(GetMainFrame(win32ui), cmdui)
Enable(cmdui, 1)
end

function OnHelpIndex(self::InteractivePythonApp, id, code)
SelectAndRunHelpFile(help)
end

thisApp = InteractivePythonApp()
abstract type AbstractMainFrame <: Abstractapp.MainFrame end
abstract type AbstractInteractivePythonApp <: Abstractapp.CApp end