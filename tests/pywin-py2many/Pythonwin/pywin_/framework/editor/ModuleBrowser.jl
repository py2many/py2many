using OrderedCollections
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.mfc.docview

import win32con
import commctrl

using win32com_.gen_py.tools: hierlist, browser
import win32com_.gen_py.framework.scriptutils
import afxres
import pyclbr
abstract type AbstractHierListCLBRModule <: Abstracthierlist.HierListItem end
abstract type AbstractHierListCLBRItem <: Abstracthierlist.HierListItem end
abstract type AbstractHierListCLBRClass <: AbstractHierListCLBRItem end
abstract type AbstractHierListCLBRFunction <: AbstractHierListCLBRItem end
abstract type AbstractHierListCLBRMethod <: AbstractHierListCLBRItem end
abstract type AbstractHierListCLBRErrorItem <: Abstracthierlist.HierListItem end
abstract type AbstractHierListCLBRErrorRoot <: AbstractHierListCLBRErrorItem end
abstract type AbstractBrowserView <: Abstractwin32com_.gen_py.mfc.docview.TreeView end
mutable struct HierListCLBRModule <: AbstractHierListCLBRModule
modName
clbrdata
end
function GetText(self::HierListCLBRModule)
return self.modName
end

function GetSubList(self::HierListCLBRModule)::Vector
ret = []
for item in values(self.clbrdata)
if item.__class__ != pyclbr.Class
push!(ret, HierListCLBRFunction(item))
else
push!(ret, HierListCLBRClass(item))
end
end
sort(ret)
return ret
end

function IsExpandable(self::HierListCLBRModule)::Int64
return 1
end

mutable struct HierListCLBRItem <: AbstractHierListCLBRItem
name::String
file
lineno
suffix
end
function __lt__(self::HierListCLBRItem, other)::Bool
return self.name < other.name
end

function __eq__(self::HierListCLBRItem, other)::Bool
return self.name == other.name
end

function GetText(self::HierListCLBRItem)::String
return self.name + self.suffix
end

function TakeDefaultAction(self::HierListCLBRItem)
if self.file
JumpToDocument(win32com_.gen_py.framework.scriptutils, self.file, self.lineno, 1)
else
SetStatusText(win32ui, "Can not locate the source code for this object.")
end
end

function PerformItemSelected(self::HierListCLBRItem)
if self.file === nothing
msg = "%s - source can not be located." % (self.name,)
else
msg = "%s defined at line %d of %s" % (self.name, self.lineno, self.file)
end
SetStatusText(win32ui, msg)
end

mutable struct HierListCLBRClass <: AbstractHierListCLBRClass
file
methods
super
suffix::String

            HierListCLBRClass(clbrclass, suffix = "") = begin
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
HierListCLBRItem(name, file, lineno, suffix)
                new(clbrclass, suffix )
            end
end
function GetSubList(self::HierListCLBRClass)::Vector
r1 = []
for c in self.super
push!(r1, HierListCLBRClass(c, " (Parent class)"))
end
sort(r1)
r2 = []
for (meth, lineno) in items(self.methods)
push!(r2, HierListCLBRMethod(meth, self.file, lineno))
end
sort(r2)
return append!(r1, r2)
end

function IsExpandable(self::HierListCLBRClass)::Int64
return length(self.methods) + length(self.super)
end

function GetBitmapColumn(self::HierListCLBRClass)::Int64
return 21
end

mutable struct HierListCLBRFunction <: AbstractHierListCLBRFunction
suffix::String

            HierListCLBRFunction(clbrfunc, suffix = "") = begin
                HierListCLBRItem(name, file, lineno, suffix)
                new(clbrfunc, suffix )
            end
end
function GetBitmapColumn(self::HierListCLBRFunction)::Int64
return 22
end

mutable struct HierListCLBRMethod <: AbstractHierListCLBRMethod

end
function GetBitmapColumn(self::HierListCLBRMethod)::Int64
return 22
end

mutable struct HierListCLBRErrorItem <: AbstractHierListCLBRErrorItem
text
end
function GetText(self::HierListCLBRErrorItem)
return self.text
end

function GetSubList(self::HierListCLBRErrorItem)
return [HierListCLBRErrorItem(self.text)]
end

function IsExpandable(self::HierListCLBRErrorItem)::Int64
return 0
end

mutable struct HierListCLBRErrorRoot <: AbstractHierListCLBRErrorRoot

end
function IsExpandable(self::HierListCLBRErrorRoot)::Int64
return 1
end

mutable struct BrowserView <: AbstractBrowserView
list
bDirty::Int64
destroying::Int64
rootitem::Union[Union[Union[Union[Union[HierListCLBRErrorRoot,HierListCLBRModule],HierListCLBRErrorRoot],HierListCLBRErrorRoot],HierListCLBRModule],HierListCLBRErrorRoot]
root::Union[Union[Union[Union[Union[HierListCLBRErrorRoot,HierListCLBRModule],HierListCLBRErrorRoot],HierListCLBRErrorRoot],HierListCLBRModule],HierListCLBRErrorRoot]
OnSize
end
function OnInitialUpdate(self::BrowserView)
self.list = nothing
rc = OnInitialUpdate(self._obj_)
HookMessage(self, self.OnSize, win32con.WM_SIZE)
self.bDirty = 0
self.destroying = 0
return rc
end

function DestroyBrowser(self::BrowserView)
DestroyList(self)
end

function OnActivateView(self::BrowserView, activate, av, dv)
if activate
CheckRefreshList(self)
end
return OnActivateView(self._obj_, activate, av, dv)
end

function _MakeRoot(self::BrowserView)::Union[Union[Union[Union[Union[HierListCLBRErrorRoot,HierListCLBRModule],HierListCLBRErrorRoot],HierListCLBRErrorRoot],HierListCLBRModule],HierListCLBRErrorRoot]
path = GetPathName(GetDocument(self))
if !(path)
return HierListCLBRErrorRoot("Error: Can not browse a file until it is saved")
else
mod, path = GetPackageModuleName(win32com_.gen_py.framework.scriptutils, path)
if self.bDirty != 0
what = "Refreshing"
try
#Delete Unsupported
del(pyclbr._modules)
catch exn
if exn isa (KeyError, AttributeError)
#= pass =#
end
end
else
what = "Building"
end
SetStatusText(win32ui, "%s class list - please wait..." % (what,), 1)
DoWaitCursor(win32ui, 1)
try
reader = pyclbr.readmodule_ex
catch exn
if exn isa AttributeError
reader = pyclbr.readmodule
end
end
try
data = reader(mod, [path])
if data
return HierListCLBRModule(mod, data)
else
return HierListCLBRErrorRoot("No Python classes in module.")
end
finally
DoWaitCursor(win32ui, 0)
SetStatusText(win32ui, LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE))
end
end
end

function DestroyList(self::BrowserView)
self.destroying = 1
list = (hasfield(typeof(self), :list) ? 
                getfield(self, :list) : nothing)
self.list = nothing
if list != nothing
HierTerm(list)
end
self.destroying = 0
end

function CheckMadeList(self::BrowserView)
if self.list != nothing || self.destroying
return
end
self.rootitem = _MakeRoot(self)
root = _MakeRoot(self)
self.list = HierListWithItems(hierlist, root, win32ui.IDB_BROWSER_HIER)
list = HierListWithItems(hierlist, root, win32ui.IDB_BROWSER_HIER)
HierInit(list, GetParentFrame(self), self)
SetStyle(list, (commctrl.TVS_HASLINES | commctrl.TVS_LINESATROOT) | commctrl.TVS_HASBUTTONS)
end

function CheckRefreshList(self::BrowserView)
if self.bDirty != 0
if self.list === nothing
CheckMadeList(self)
else
new_root = _MakeRoot(self)
if self.rootitem.__class__ == new_root.__class__ == HierListCLBRModule
self.rootitem.modName = new_root.modName
self.rootitem.clbrdata = new_root.clbrdata
Refresh(self.list)
else
AcceptRoot(self.list, _MakeRoot(self))
end
end
self.bDirty = 0
end
end

function OnSize(self::BrowserView, params)::Int64
lparam = params[4]
w = LOWORD(win32api, lparam)
h = HIWORD(win32api, lparam)
if w != 0
CheckMadeList(self)
elseif w == 0
DestroyList(self)
end
return 1
end

function _UpdateUIForState(self::BrowserView)
self.bDirty = 1
end
