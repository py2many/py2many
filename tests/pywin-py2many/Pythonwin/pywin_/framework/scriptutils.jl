#= 
Various utilities for running/importing a script
 =#
using Printf
using PyCall
using StringEncodings
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.debugger
using win32com_.gen_py.framework: interact
using importlib: reload
import io as io



import win32con
import __main__
using win32com_.gen_py.mfc: dialog
using win32com_.gen_py.mfc.docview: TreeView

import string

import linecache
import bdb
using cmdline: ParseArgs
abstract type AbstractDlgRunScript <: Abstractdialog.Dialog end
RS_DEBUGGER_NONE = 0
RS_DEBUGGER_STEP = 1
RS_DEBUGGER_GO = 2
RS_DEBUGGER_PM = 3
debugging_options = split("No debugging\nStep-through in the debugger\nRun in the debugger\nPost-Mortem of unhandled exceptions", "\n")
byte_cr = encode("\r", "ascii")
byte_lf = encode("\n", "ascii")
byte_crlf = encode("\r\n", "ascii")
mutable struct DlgRunScript <: AbstractDlgRunScript
#= A class for the 'run script' dialog =#
bHaveDebugger

            DlgRunScript(bHaveDebugger) = begin
                dialog.Dialog.__init__(self, win32ui.IDD_RUN_SCRIPT)
AddDDX(win32ui.IDC_EDIT1, "script")
AddDDX(win32ui.IDC_EDIT2, "args")
AddDDX(win32ui.IDC_COMBO1, "debuggingType", "i")
HookCommand(OnBrowse, win32ui.IDC_BUTTON2)
                new(bHaveDebugger)
            end
end
function OnInitDialog(self::DlgRunScript)
rc = OnInitDialog(dialog.Dialog)
cbo = GetDlgItem(self, win32ui.IDC_COMBO1)
for o in debugging_options
AddString(cbo, o)
end
SetCurSel(cbo, self["debuggingType"])
if !(self.bHaveDebugger)
EnableWindow(cbo, 0)
end
end

function OnBrowse(self::DlgRunScript, id, cmd)::Int64
openFlags = win32con.OFN_OVERWRITEPROMPT | win32con.OFN_FILEMUSTEXIST
dlg = CreateFileDialog(win32ui, 1, nothing, nothing, openFlags, "Python Scripts (*.py)|*.py||", self)
SetOFNTitle(dlg, "Run Script")
if DoModal(dlg) != win32con.IDOK
return 0
end
self["script"] = GetPathName(dlg)
UpdateData(self, 0)
return 0
end

function GetDebugger()
#= Get the default Python debugger.  Returns the debugger, or None.

    It is assumed the debugger has a standard "pdb" defined interface.
    Currently always returns the 'win32com_.gen_py.debugger' debugger, or None
    (pdb is _not_ returned as it is not effective in this GUI environment)
     =#
try
return win32com_.gen_py.debugger
catch exn
if exn isa ImportError
return nothing
end
end
end

function IsOnPythonPath(path)::Int64
#= Given a path only, see if it is on the Pythonpath.  Assumes path is a full path spec. =#
for syspath in sys.path
try
if syspath && FullPath(win32ui, syspath) == path
return 1
end
catch exn
 let details = exn
if details isa win32ui.error
@printf("Warning: The sys.path entry \'%s\' is invalid\n%s\n", syspath, details)
end
end
end
end
return 0
end

function GetPackageModuleName(fileName)::Tuple
#= Given a filename, return (module name, new path).
    eg - given "c:\a\b\c\my.py", return ("b.c.my",None) if "c:\a" is on sys.path.
    If no package found, will return ("my", "c:\a\b\c")
     =#
path, fname = split(os.path, fileName)
path = FullPath(win32ui, path)
origPath = FullPath(win32ui, path)
fname = splitext(os.path, fname)[1]
modBits = []
newPathReturn = nothing
if !IsOnPythonPath(path) != 0
while length(path) > 3
path, modBit = split(os.path, path)
push!(modBits, modBit)
if IsOnPythonPath(path) && modBit ∈ sys.modules && exists(os.path, join) || exists(os.path, join) || exists(os.path, join)
reverse(modBits)
return ((join(modBits, ".") + ".") + fname, newPathReturn)
end
end
end
return (fname, newPathReturn)
end

function GetActiveView()
#= Gets the edit control (eg, EditView) with the focus, or None =#
try
childFrame, bIsMaximised = MDIGetActive(GetMainFrame(win32ui))
return GetActiveView()
catch exn
if exn isa win32ui.error
return nothing
end
end
end

function GetActiveEditControl()
view = GetActiveView()
if view === nothing
return nothing
end
if hasfield(typeof(view), :SCIAddText)
return view
end
try
return GetRichEditCtrl(view)
catch exn
if exn isa AttributeError
#= pass =#
end
end
try
return GetEditCtrl(view)
catch exn
if exn isa AttributeError
#= pass =#
end
end
end

function GetActiveEditorDocument()::Tuple
#= Returns the active editor document and view, or (None,None) if no
    active document or its not an editor document.
     =#
view = GetActiveView()
if view === nothing || isa(view, TreeView)
return (nothing, nothing)
end
doc = GetDocument(view)
if hasfield(typeof(doc), :MarkerAdd)
return (doc, view)
end
return (nothing, nothing)
end

function GetActiveFileName(bAutoSave = 1)
#= Gets the file name for the active frame, saving it if necessary.

    Returns None if it cant be found, or raises KeyboardInterrupt.
     =#
pathName = nothing
active = GetActiveView()
if active === nothing
return nothing
end
try
doc = GetDocument(active)
pathName = GetPathName(doc)
if bAutoSave && length(pathName) > 0 || GetTitle(doc)[begin:8] == "Untitled" || GetTitle(doc)[begin:6] == "Script"
if IsModified(doc)
try
OnSaveDocument(doc, pathName)
pathName = GetPathName(doc)
clearcache(linecache)
catch exn
if exn isa win32ui.error
throw(KeyboardInterrupt)
end
end
end
end
catch exn
if exn isa (win32ui.error, AttributeError)
#= pass =#
end
end
if !(pathName)
return nothing
end
return pathName
end

lastScript = ""
lastArgs = ""
lastDebuggingType = RS_DEBUGGER_NONE
function RunScript(defName = nothing, defArgs = nothing, bShowDialog = 1, debuggingType = nothing)
global lastScript, lastArgs, lastDebuggingType
_debugger_stop_frame_ = 1
debugger = GetDebugger()
if defName === nothing
try
pathName = GetActiveFileName()
catch exn
if exn isa KeyboardInterrupt
return
end
end
else
pathName = defName
end
if !(pathName)
pathName = lastScript
end
if defArgs === nothing
args = ""
if pathName == lastScript
args = lastArgs
end
else
args = defArgs
end
if debuggingType === nothing
debuggingType = lastDebuggingType
end
if !(pathName) || bShowDialog
dlg = DlgRunScript(debugger != nothing)
dlg["script"] = pathName
dlg["args"] = args
dlg["debuggingType"] = debuggingType
if DoModal(dlg) != win32con.IDOK
return
end
script = dlg["script"]
args = dlg["args"]
debuggingType = dlg["debuggingType"]
if !(script)
return
end
if debuggingType == RS_DEBUGGER_GO && debugger != nothing
try
rd = _GetCurrentDebugger(debugger)
catch exn
if exn isa AttributeError
rd = nothing
end
end
if rd != nothing && length(rd.breaks) == 0
msg = "There are no active break-points.\r\n\r\nSelecting this debug option without any\r\nbreak-points is unlikely to have the desired effect\r\nas the debugger is unlikely to be invoked..\r\n\r\nWould you like to step-through in the debugger instead?"
rc = MessageBox(win32ui, msg, LoadString(win32ui, win32ui.IDR_DEBUGGER), win32con.MB_YESNOCANCEL | win32con.MB_ICONINFORMATION)
if rc == win32con.IDCANCEL
return
end
if rc == win32con.IDYES
debuggingType = RS_DEBUGGER_STEP
end
end
end
lastDebuggingType = debuggingType
lastScript = script
lastArgs = args
else
script = pathName
end
if length(splitext(os.path, script)[2]) == 0
script = script * ".py"
end
path, fnameonly = split(os.path, script)
if length(path) == 0
try
stat(os, fnameonly)
script = fnameonly
catch exn
if exn isa os.error
fullScript = LocatePythonFile(script)
if fullScript === nothing
MessageBox(win32ui, "The file \'%s\' can not be located" % script)
return
end
script = fullScript
end
end
else
path = FullPath(win32ui, path)
if !IsOnPythonPath(path) != 0
append(sys.path, path)
end
end
try
f = readline(script)
catch exn
 let exc = exn
if exc isa IOError
MessageBox(win32ui, "The file could not be opened - %s (%d)" % (exc.strerror, exc.errno))
return
end
end
end
code = replace(replace(read(f), byte_crlf, byte_lf), byte_cr, byte_lf) + byte_lf
oldArgv = append!([PROGRAM_FILE], ARGS)
append!([PROGRAM_FILE], ARGS) = ParseArgs(args)
insert(sys.argv, 0, script)
oldPath0 = sys.path[1]
newPath0 = split(os.path, script)[1]
if !(oldPath0)
sys.path[1] = newPath0
insertedPath0 = 0
else
insert(sys.path, 0, newPath0)
insertedPath0 = 1
end
bWorked = 0
DoWaitCursor(win32ui, 1)
base = split(os.path, script)[2]
PumpWaitingMessages(win32ui)
SetStatusText(win32ui, "Running script %s..." % base, 1)
exitCode = 0
if debugger === nothing && debuggingType != RS_DEBUGGER_NONE
MessageBox(win32ui, "No debugger is installed.  Debugging options have been ignored!")
debuggingType = RS_DEBUGGER_NONE
end
try
codeObject = compile(code, script, "exec")
catch exn
_HandlePythonFailure("run script", script)
return
end
__main__.__file__ = script
try
if debuggingType == RS_DEBUGGER_STEP
run(debugger, codeObject, __main__.__dict__, 1)
elseif debuggingType == RS_DEBUGGER_GO
run(debugger, codeObject, __main__.__dict__, 0)
else
exec(codeObject, __main__.__dict__)
end
bWorked = 1
catch exn
if exn isa bdb.BdbQuit
println("Debugging session cancelled.")
exitCode = 1
bWorked = 1
end
 let code = exn
if code isa SystemExit
exitCode = code
bWorked = 1
end
end
if exn isa KeyboardInterrupt
if interact.edit && interact.edit.currentView
EnsureNoPrompt(interact.edit.currentView)
end
current_exceptions() != [] ? current_exceptions()[end] : nothing
if interact.edit && interact.edit.currentView
AppendToPrompt(interact.edit.currentView, [])
end
bWorked = 1
end
if interact.edit && interact.edit.currentView
EnsureNoPrompt(interact.edit.currentView)
end
current_exceptions() != [] ? current_exceptions()[end] : nothing
if interact.edit && interact.edit.currentView
AppendToPrompt(interact.edit.currentView, [])
end
if debuggingType == RS_DEBUGGER_PM
pm(debugger)
end
end
#Delete Unsupported
del(__main__.__file__)
append!([PROGRAM_FILE], ARGS) = oldArgv
if insertedPath0
#Delete Unsupported
del(sys.path)
else
sys.path[1] = oldPath0
end
close(f)
if bWorked != 0
SetStatusText(win32ui, "Script \'%s\' returned exit code %s" % (script, exitCode))
else
SetStatusText(win32ui, "Exception raised while running script  %s" % base)
end
try
flush(sys.stdout)
catch exn
if exn isa AttributeError
#= pass =#
end
end
DoWaitCursor(win32ui, 0)
end

function ImportFile()::Int64
#= This code looks for the current window, and determines if it can be imported.  If not,
    it will prompt for a file name, and allow it to be imported. =#
try
pathName = GetActiveFileName()
catch exn
if exn isa KeyboardInterrupt
pathName = nothing
end
end
if pathName != nothing
if lower(splitext(os.path, pathName)[2]) ∉ (".py", ".pyw", ".pyx")
pathName = nothing
end
end
if pathName === nothing
openFlags = win32con.OFN_OVERWRITEPROMPT | win32con.OFN_FILEMUSTEXIST
dlg = CreateFileDialog(win32ui, 1, nothing, nothing, openFlags, "Python Scripts (*.py;*.pyw)|*.py;*.pyw;*.pyx||")
SetOFNTitle(dlg, "Import Script")
if DoModal(dlg) != win32con.IDOK
return 0
end
pathName = GetPathName(dlg)
end
path, modName = split(os.path, pathName)
modName, modExt = splitext(os.path, modName)
newPath = nothing
has_break = false
for (key, mod) in collect(items(sys.modules))
if (hasfield(typeof(mod), :__file__) ? 
                getfield(mod, :__file__) : nothing)
fname = mod.__file__
base, ext = splitext(os.path, fname)
if lower(ext) ∈ [".pyo", ".pyc"]
ext = ".py"
end
fname = base + ext
if ComparePath(win32ui, fname, pathName)
modName = key
has_break = true
break;
end
end
end
if has_break != true
modName, newPath = GetPackageModuleName(pathName)
if newPath
append(sys.path, newPath)
end
end
if modName ∈ sys.modules
bNeedReload = 1
what = "reload"
else
what = "import"
bNeedReload = 0
end
SetStatusText(win32ui, capitalize(what) + "ing module...", 1)
DoWaitCursor(win32ui, 1)
try
codeObj = compile("import " + modName, "<auto import>", "exec")
catch exn
if exn isa SyntaxError
SetStatusText(win32ui, ("Invalid filename for import: \"" + modName) * "\"")
return
end
end
try
exec(codeObj, __main__.__dict__)
mod = get(sys.modules, modName)
if bNeedReload
mod = reload(sys.modules[modName + 1])
end
SetStatusText(win32ui, (("Successfully " + what) * "ed module \'" + modName) * ("\': %s" % (hasfield(typeof(mod), :__file__) ? 
                getfield(mod, :__file__) : "<unkown file>")))
catch exn
_HandlePythonFailure(what)
end
DoWaitCursor(win32ui, 0)
end

function CheckFile()
#= This code looks for the current window, and gets Python to check it
    without actually executing any code (ie, by compiling only)
     =#
try
pathName = GetActiveFileName()
catch exn
if exn isa KeyboardInterrupt
return
end
end
what = "check"
SetStatusText(win32ui, capitalize(what) + "ing module...", 1)
DoWaitCursor(win32ui, 1)
try
f = readline(pathName)
catch exn
 let details = exn
if details isa IOError
@printf("Cant open file \'%s\' - %s\n", pathName, details)
return
end
end
end
try
code = read(f) + "\n"
finally
close(f)
end
try
codeObj = compile(code, pathName, "exec")
if RunTabNanny(pathName)
SetStatusText(win32ui, ("Python and the TabNanny successfully checked the file \'" + basename(os.path, pathName)) * "\'")
end
catch exn
if exn isa SyntaxError
_HandlePythonFailure(what, pathName)
end
current_exceptions() != [] ? current_exceptions()[end] : nothing
_HandlePythonFailure(what)
end
DoWaitCursor(win32ui, 0)
end

function RunTabNanny(filename)::Int64
tabnanny = FindTabNanny()
if tabnanny === nothing
MessageBox(win32ui, "The TabNanny is not around, so the children can run amok!")
return
end
newout = StringIO(io)
old_out = (sys.stderr, sys.stdout)
sys.stderr = newout
sys.stdout = newout
try
check(tabnanny, filename)
finally
sys.stderr, sys.stdout = old_out
end
data = getvalue(newout)
if data
try
lineno = split(data)[2]
lineno = parse(Int, lineno)
_JumpToPosition(filename, lineno)
try
SCISetViewWS(GetActiveEditControl(), 1)
catch exn
#= pass =#
end
SetStatusText(win32ui, "The TabNanny found trouble at line %d" % lineno)
catch exn
if exn isa (IndexError, TypeError, ValueError)
println("The tab nanny complained, but I cant see where!")
println(data)
end
end
return 0
end
return 1
end

function _JumpToPosition(fileName, lineno, col = 1)
JumpToDocument(fileName, lineno, col)
end

function JumpToDocument(fileName, lineno = 0, col = 1, nChars = 0, bScrollToTop = 0)
doc = OpenDocumentFile(GetApp(win32ui), fileName)
if doc === nothing
return nothing
end
frame = GetParentFrame(GetFirstView(doc))
try
view = GetEditorView(frame)
if GetActiveView() != view
SetActiveView(frame, view)
end
AutoRestore(frame)
catch exn
if exn isa AttributeError
view = GetFirstView(doc)
end
end
if lineno > 0
charNo = LineIndex(view, lineno - 1)
start = (charNo + col) - 1
size = GetTextLength(view)
try
EnsureCharsVisible(view, charNo)
catch exn
if exn isa AttributeError
println("Doesnt appear to be one of our views?")
end
end
SetSel(view, min(start, size), min(start + nChars, size))
end
if bScrollToTop
curTop = GetFirstVisibleLine(view)
nScroll = (lineno - 1) - curTop
LineScroll(view, nScroll, 0)
end
SetFocus(view)
return view
end

function _HandlePythonFailure(what, syntaxErrorPathName = nothing)
typ, details, tb = exc_info(sys)
if isa(details, SyntaxError)
try
msg, (fileName, line, col, text) = details
if !(fileName) || fileName == "<string>" && syntaxErrorPathName
fileName = syntaxErrorPathName
end
_JumpToPosition(fileName, line, col)
catch exn
if exn isa (TypeError, ValueError)
msg = string(details)
end
end
SetStatusText(win32ui, ("Failed to " + what) * (" - syntax error - %s" % msg))
else
current_exceptions() != [] ? current_exceptions()[end] : nothing
SetStatusText(win32ui, ("Failed to " + what) * " - " * string(details))
end
tb = nothing
end

function FindTabNanny()
try
return __import__("tabnanny")
catch exn
if exn isa ImportError
#= pass =#
end
end
filename = "tabnanny.py"
try
path = RegQueryValue(win32api, win32con.HKEY_LOCAL_MACHINE, "SOFTWARE\\Python\\PythonCore\\%s\\InstallPath" % sys.winver)
catch exn
if exn isa win32api.error
println("WARNING - The Python registry does not have an \'InstallPath\' setting")
@printf("          The file \'%s\' can not be located\n", filename)
return nothing
end
end
fname = join
try
stat(os, fname)
catch exn
if exn isa os.error
@printf("WARNING - The file \'%s\' can not be located in path \'%s\'\n", filename, path)
return nothing
end
end
tabnannyhome, tabnannybase = split(os.path, fname)
tabnannybase = splitext(os.path, tabnannybase)[1]
insert(sys.path, 0, tabnannyhome)
try
return __import__(tabnannybase)
finally
#Delete Unsupported
del(sys.path)
end
end

function LocatePythonFile(fileName, bBrowseIfDir = 1)
#= Given a file name, return a fully qualified file name, or None =#
if !isfile(os.path, fileName)
baseName = fileName
has_break = false
for path in sys.path
fileName = abspath(os.path, join)
if isdir(os.path, fileName)
if bBrowseIfDir
d = CreateFileDialog(win32ui, 1, "*.py", nothing, 0, "Python Files (*.py)|*.py|All files|*.*")
SetOFNInitialDir(d, fileName)
rc = DoModal(d)
if rc == win32con.IDOK
fileName = GetPathName(d)
has_break = true
break;
else
return nothing
end
end
else
fileName = fileName * ".py"
if isfile(os.path, fileName)
has_break = true
break;
end
end
end
if has_break != true
return nothing
end
end
return FullPath(win32ui, fileName)
end
