using OrderedCollections
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.docking.DockingBar
import regutil
include("hierlist.jl")
import win32con
import commctrl
using win32com_.gen_py.mfc: dialog
import glob
import pyclbr
import win32com_.gen_py.framework.scriptutils
import afxres
abstract type AbstractHLIErrorItem <: Abstracthierlist.HierListItem end
abstract type AbstractHLICLBRItem <: Abstracthierlist.HierListItem end
abstract type AbstractHLICLBRClass <: AbstractHLICLBRItem end
abstract type AbstractHLICLBRFunction <: AbstractHLICLBRClass end
abstract type AbstractHLICLBRMethod <: AbstractHLICLBRItem end
abstract type AbstractHLIModuleItem <: Abstracthierlist.HierListItem end
abstract type AbstractHLIDirectoryItem <: Abstracthierlist.HierListItem end
abstract type AbstractHLIProjectRoot <: Abstracthierlist.HierListItem end
abstract type AbstractHLIRoot <: Abstracthierlist.HierListItem end
abstract type Abstractdynamic_browser <: Abstractdialog.Dialog end
mutable struct HLIErrorItem <: AbstractHLIErrorItem
text

            HLIErrorItem(text) = begin
                hierlist.HierListItem.__init__(self)
                new(text)
            end
end
function GetText(self::HLIErrorItem)
return self.text
end

mutable struct HLICLBRItem <: AbstractHLICLBRItem
name
file
lineno
suffix
end
function __lt__(self::HLICLBRItem, other)::Bool
return self.name < other.name
end

function __eq__(self::HLICLBRItem, other)::Bool
return self.name == other.name
end

function GetText(self::HLICLBRItem)::Any
return self.name + self.suffix
end

function TakeDefaultAction(self::HLICLBRItem)
if self.file
JumpToDocument(win32com_.gen_py.framework.scriptutils, self.file, self.lineno, 1)
else
SetStatusText(win32ui, "The source of this object is unknown")
end
end

function PerformItemSelected(self::HLICLBRItem)
if self.file === nothing
msg = "%s - source can not be located." % (self.name,)
else
msg = "%s defined at line %d of %s" % (self.name, self.lineno, self.file)
end
SetStatusText(win32ui, msg)
end

mutable struct HLICLBRClass <: AbstractHLICLBRClass
file
methods
super
suffix::String

            HLICLBRClass(clbrclass, suffix = "") = begin
                try
name = clbrclass.name
file = clbrclass.file
lineno = clbrclass.lineno
super = clbrclass.super
methods = clbrclass.methods
catch exn
if exn isa AttributeError
name = clbrclass
file = nothing
lineno = nothing
super = []
methods = OrderedDict()
end
end
HLICLBRItem(name, file, lineno, suffix)
                new(clbrclass, suffix )
            end
end
function GetSubList(self::HLICLBRClass)::Vector
ret = []
for c in self.super
push!(ret, HLICLBRClass(c, " (Parent class)"))
end
for (meth, lineno) in items(self.methods)
push!(ret, HLICLBRMethod(meth, self.file, lineno, " (method)"))
end
return ret
end

function IsExpandable(self::HLICLBRClass)::Int64
return length(self.methods) + length(self.super)
end

function GetBitmapColumn(self::HLICLBRClass)::Int64
return 21
end

mutable struct HLICLBRFunction <: AbstractHLICLBRFunction

end
function GetBitmapColumn(self::HLICLBRFunction)::Int64
return 22
end

mutable struct HLICLBRMethod <: AbstractHLICLBRMethod

end
function GetBitmapColumn(self::HLICLBRMethod)::Int64
return 22
end

mutable struct HLIModuleItem <: AbstractHLIModuleItem
path

            HLIModuleItem(path) = begin
                hierlist.HierListItem.__init__(self)
                new(path)
            end
end
function GetText(self::HLIModuleItem)::String
return split(os.path, self.path)[2] + " (module)"
end

function IsExpandable(self::HLIModuleItem)::Int64
return 1
end

function TakeDefaultAction(self::HLIModuleItem)
OpenDocumentFile(GetApp(win32ui), self.path)
end

function GetBitmapColumn(self::HLIModuleItem)::Int64
col = 4
try
if GetFileAttributes(win32api, self.path) & win32con.FILE_ATTRIBUTE_READONLY
col = 5
end
catch exn
if exn isa win32api.error
#= pass =#
end
end
return col
end

function GetSubList(self::HLIModuleItem)::Vector
mod, path = GetPackageModuleName(win32com_.gen_py.framework.scriptutils, self.path)
SetStatusText(win32ui, "Building class list - please wait...", 1)
DoWaitCursor(win32ui, 1)
try
try
reader = pyclbr.readmodule_ex
extra_msg = " or functions"
catch exn
if exn isa AttributeError
reader = pyclbr.readmodule
extra_msg = ""
end
end
data = reader(mod, [path])
if data
ret = []
for item in values(data)
if item.__class__ != pyclbr.Class
push!(ret, HLICLBRFunction(item, " (function)"))
else
push!(ret, HLICLBRClass(item, " (class)"))
end
end
sort(ret)
return ret
else
return [HLIErrorItem("No Python classes%s in module." % (extra_msg,))]
end
finally
DoWaitCursor(win32ui, 0)
SetStatusText(win32ui, LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE))
end
end

function MakePathSubList(path)::Vector
ret = []
for filename in glob(glob, join)
if isdir(os.path, filename) && isfile(os.path, join)
push!(ret, HLIDirectoryItem(filename, split(os.path, filename)[2]))
elseif lower(splitext(os.path, filename)[2]) ∈ [".py", ".pyw"]
push!(ret, HLIModuleItem(filename))
end
end
return ret
end

mutable struct HLIDirectoryItem <: AbstractHLIDirectoryItem
path
bSubDirs
displayName

            HLIDirectoryItem(path, displayName = nothing, bSubDirs = 0) = begin
                hierlist.HierListItem.__init__(self)
if displayName
displayName = displayName
else
displayName = path
end
                new(path, displayName , bSubDirs )
            end
end
function IsExpandable(self::HLIDirectoryItem)::Int64
return 1
end

function GetText(self::HLIDirectoryItem)
return self.displayName
end

function GetSubList(self::HLIDirectoryItem)::Vector
ret = MakePathSubList(self.path)
if split(os.path, self.path)[2] == "win32com_"
try
path = GetFullPathName(win32api, join)
ret = append!(ret, MakePathSubList(path))
catch exn
if exn isa win32ui.error
#= pass =#
end
end
end
return ret
end

mutable struct HLIProjectRoot <: AbstractHLIProjectRoot
projectName
displayName

            HLIProjectRoot(projectName, displayName = nothing) = begin
                hierlist.HierListItem.__init__(self)
                new(projectName, displayName )
            end
end
function GetText(self::HLIProjectRoot)
return self.displayName
end

function IsExpandable(self::HLIProjectRoot)::Int64
return 1
end

function GetSubList(self::HLIProjectRoot)
paths = GetRegisteredNamedPath(regutil, self.projectName)
pathList = split(paths, ";")
if length(pathList) == 1
ret = MakePathSubList(pathList[1])
else
ret = collect(map(HLIDirectoryItem, pathList))
end
return ret
end

mutable struct HLIRoot <: AbstractHLIRoot


            HLIRoot() = begin
                hierlist.HierListItem.__init__(self)
                new()
            end
end
function IsExpandable(self::HLIRoot)::Int64
return 1
end

function GetSubList(self::HLIRoot)::Vector
keyStr = BuildDefaultPythonKey(regutil) + "\\PythonPath"
hKey = RegOpenKey(win32api, GetRootKey(regutil), keyStr)
try
ret = []
push!(ret, HLIProjectRoot("", "Standard Python Library"))
index = 0
while true
try
push!(ret, HLIProjectRoot(RegEnumKey(win32api, hKey, index)))
index = index + 1
catch exn
if exn isa win32api.error
break;
end
end
end
return ret
finally
RegCloseKey(win32api, hKey)
end
end

mutable struct dynamic_browser <: Abstractdynamic_browser
hier_list
cs
dt::Vector{Union{Vector{Union{Any, Tuple{Int64}, String, Tuple{Union{Int64, String}}}}, Vector{Union{Any, Tuple{Int64}, String}}}}
style

            dynamic_browser(hli_root, cs = (((win32con.WS_CHILD | win32con.WS_VISIBLE) | commctrl.TVS_HASLINES) | commctrl.TVS_LINESATROOT) | commctrl.TVS_HASBUTTONS, dt::Vector{Union{Vector{Union{Any, Tuple{Int64}, String, Tuple{Union{Int64, String}}}}, Vector{Union{Any, Tuple{Int64}, String}}}} = [["Python Projects", (0, 0, 200, 200), style, nothing, (8, "MS Sans Serif")], ["SysTreeView32", nothing, win32ui.IDC_LIST1, (0, 0, 200, 200), cs]], style = win32con.WS_OVERLAPPEDWINDOW | win32con.WS_VISIBLE) = begin
                dialog.Dialog.__init__(self, dt)
HookMessage(on_size, win32con.WM_SIZE)
                new(hli_root, cs , dt, style )
            end
end
function OnInitDialog(self::dynamic_browser)
HierInit(self.hier_list, self)
return OnInitDialog(dialog.Dialog)
end

function on_size(self::dynamic_browser, params)
lparam = params[4]
w = LOWORD(win32api, lparam)
h = HIWORD(win32api, lparam)
MoveWindow(GetDlgItem(self, win32ui.IDC_LIST1), (0, 0, w, h))
end

function BrowseDialog()
root = HLIRoot()
if !IsExpandable(root)
throw(TypeError("Browse() argument must have __dict__ attribute, or be a Browser supported type"))
end
dlg = dynamic_browser(root)
CreateWindow(dlg)
end

function DockableBrowserCreator(parent)
root = HLIRoot()
hl = HierListWithItems(hierlist, root, win32ui.IDB_BROWSER_HIER)
style = ((((win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.WS_BORDER) | commctrl.TVS_HASLINES) | commctrl.TVS_LINESATROOT) | commctrl.TVS_HASBUTTONS
control = CreateTreeCtrl(win32ui)
CreateWindow(control, style, (0, 0, 150, 300), parent, win32ui.IDC_LIST1)
list = HierInit(hl, parent, control)
return control
end

function DockablePathBrowser()
bar = DockingBar(win32com_.gen_py.docking.DockingBar)
CreateWindow(bar, GetMainFrame(win32ui), DockableBrowserCreator, "Path Browser", 36362)
SetBarStyle(bar, ((GetBarStyle(bar) | afxres.CBRS_TOOLTIPS) | afxres.CBRS_FLYBY) | afxres.CBRS_SIZE_DYNAMIC)
EnableDocking(bar, afxres.CBRS_ALIGN_ANY)
DockControlBar(GetMainFrame(win32ui), bar)
end

Browse = DockablePathBrowser