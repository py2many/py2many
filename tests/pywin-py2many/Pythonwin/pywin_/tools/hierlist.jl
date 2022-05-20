using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")


import win32con


using win32com_.gen_py.mfc: object, window, docview, dialog
import commctrl
abstract type AbstractHierDialog <: Abstractdialog.Dialog end
abstract type AbstractHierList <: Abstractobject.Object end
abstract type AbstractHierListWithItems <: AbstractHierList end
abstract type AbstractHierListItem end
function GetItemText(item)
if type_(item) == type_(()) || type_(item) == type_([])
use = item[1]
else
use = item
end
if type_(use) == type_("")
return use
else
return repr(item)
end
end

mutable struct HierDialog <: AbstractHierDialog
dlgID
hierList
title
bitmapID
childListBoxID
dll

            HierDialog(title, hierList, bitmapID = win32ui.IDB_HIERFOLDERS, dlgID = win32ui.IDD_TREE, dll = nothing, childListBoxID = win32ui.IDC_LIST1) = begin
                dialog.Dialog.__init__(self, dlgID, dll)
                new(title, hierList, bitmapID , dlgID , dll , childListBoxID )
            end
end
function OnInitDialog(self::HierDialog)
SetWindowText(self, self.title)
HierInit(self.hierList, self)
return OnInitDialog(dialog.Dialog)
end

mutable struct HierList <: AbstractHierList
listControl
bitmapID
root
listBoxId
itemHandleMap::Dict
filledItemHandlesMap::Dict
bitmapMask
imageList
notify_parent
OnTreeItemExpanding
OnTreeItemSelChanged
OnTreeItemDoubleClick
end
function __getattr__(self::HierList, attr)
try
return getfield(self.listControl, :attr)
catch exn
if exn isa AttributeError
return __getattr__(object.Object, self)
end
end
end

function ItemFromHandle(self::HierList, handle)::Dict
return self.itemHandleMap[handle]
end

function SetStyle(self::HierList, newStyle)
hwnd = GetSafeHwnd(self.listControl)
style = GetWindowLong(win32api, hwnd, win32con.GWL_STYLE)
SetWindowLong(win32api, hwnd, win32con.GWL_STYLE, style | newStyle)
end

function HierInit(self::HierList, parent, listControl = nothing)
if self.bitmapMask === nothing
bitmapMask = RGB(0, 0, 255)
else
bitmapMask = self.bitmapMask
end
self.imageList = CreateImageList(win32ui, self.bitmapID, 16, 0, bitmapMask)
if listControl === nothing
if self.listBoxId === nothing
self.listBoxId = win32ui.IDC_LIST1
end
self.listControl = GetDlgItem(parent, self.listBoxId)
else
self.listControl = listControl
lbid = GetDlgCtrlID(listControl)
@assert(self.listBoxId === nothing || self.listBoxId == lbid)
self.listBoxId = lbid
end
SetImageList(self.listControl, self.imageList, commctrl.LVSIL_NORMAL)
if sys.version_info[1] < 3
HookNotify(parent, self.OnTreeItemExpanding, commctrl.TVN_ITEMEXPANDINGA)
HookNotify(parent, self.OnTreeItemSelChanged, commctrl.TVN_SELCHANGEDA)
else
HookNotify(parent, self.OnTreeItemExpanding, commctrl.TVN_ITEMEXPANDINGW)
HookNotify(parent, self.OnTreeItemSelChanged, commctrl.TVN_SELCHANGEDW)
end
HookNotify(parent, self.OnTreeItemDoubleClick, commctrl.NM_DBLCLK)
self.notify_parent = parent
if self.root
AcceptRoot(self, self.root)
end
end

function DeleteAllItems(self::HierList)
DeleteAllItems(self.listControl)
self.root = nothing
self.itemHandleMap = Dict()
self.filledItemHandlesMap = Dict()
end

function HierTerm(self::HierList)
parent = self.notify_parent
if sys.version_info[1] < 3
HookNotify(parent, nothing, commctrl.TVN_ITEMEXPANDINGA)
HookNotify(parent, nothing, commctrl.TVN_SELCHANGEDA)
else
HookNotify(parent, nothing, commctrl.TVN_ITEMEXPANDINGW)
HookNotify(parent, nothing, commctrl.TVN_SELCHANGEDW)
end
HookNotify(parent, nothing, commctrl.NM_DBLCLK)
DeleteAllItems(self)
self.listControl = nothing
self.notify_parent = nothing
end

function OnTreeItemDoubleClick(self::HierList, info, extra)::Int64
hwndFrom, idFrom, code = info
if idFrom != self.listBoxId
return nothing
end
item = self.itemHandleMap[GetSelectedItem(self.listControl)]
TakeDefaultAction(self, item)
return 1
end

function OnTreeItemExpanding(self::HierList, info, extra)::Int64
hwndFrom, idFrom, code = info
if idFrom != self.listBoxId
return nothing
end
action, itemOld, itemNew, pt = extra
itemHandle = itemNew[1]
if itemHandle ∉ self.filledItemHandlesMap
item = self.itemHandleMap[itemHandle]
AddSubList(self, itemHandle, GetSubList(self, item))
self.filledItemHandlesMap[itemHandle] = nothing
end
return 0
end

function OnTreeItemSelChanged(self::HierList, info, extra)::Int64
hwndFrom, idFrom, code = info
if idFrom != self.listBoxId
return nothing
end
action, itemOld, itemNew, pt = extra
itemHandle = itemNew[1]
item = self.itemHandleMap[itemHandle]
PerformItemSelected(self, item)
return 1
end

function AddSubList(self::HierList, parentHandle, subItems)
for item in subItems
AddItem(self, parentHandle, item)
end
end

function AddItem(self::HierList, parentHandle, item, hInsertAfter = commctrl.TVI_LAST)
text = GetText(self, item)
if IsExpandable(self, item)
cItems = 1
else
cItems = 0
end
bitmapCol = GetBitmapColumn(self, item)
bitmapSel = GetSelectedBitmapColumn(self, item)
if bitmapSel === nothing
bitmapSel = bitmapCol
end
hitem = InsertItem(self.listControl, parentHandle, hInsertAfter, (nothing, nothing, nothing, text, bitmapCol, bitmapSel, cItems, 0))
self.itemHandleMap[hitem] = item
return hitem
end

function _GetChildHandles(self::HierList, handle)::Vector
ret = []
try
handle = GetChildItem(self.listControl, handle)
while true
push!(ret, handle)
handle = GetNextItem(self.listControl, handle, commctrl.TVGN_NEXT)
end
catch exn
if exn isa win32ui.error
#= pass =#
end
end
return ret
end

function ItemFromHandle(self::HierList, handle)::Dict
return self.itemHandleMap[handle]
end

function Refresh(self::HierList, hparent = nothing)
if hparent === nothing
hparent = commctrl.TVI_ROOT
end
if hparent ∉ self.filledItemHandlesMap
return
end
root_item = self.itemHandleMap[hparent]
old_handles = _GetChildHandles(self, hparent)
old_items = collect(map(self.ItemFromHandle, old_handles))
new_items = GetSubList(self, root_item)
inew = 0
hAfter = commctrl.TVI_FIRST
for iold in 0:length(old_items) - 1
inewlook = inew
matched = 0
while inewlook < length(new_items)
if old_items[iold + 1] == new_items[inewlook + 1]
matched = 1
has_break = true
break;
end
inewlook = inewlook + 1
end
if matched != 0
for i in inew:inewlook - 1
hAfter = AddItem(self, hparent, new_items[i + 1], hAfter)
end
inew = inewlook + 1
hold = old_handles[iold + 1]
if hold ∈ self.filledItemHandlesMap
Refresh(self, hold)
end
else
hdelete = old_handles[iold + 1]
for hchild in _GetChildHandles(self, hdelete)
delete!(self.itemHandleMap, hchild)
if hchild ∈ self.filledItemHandlesMap
delete!(self.filledItemHandlesMap, hchild)
end
end
DeleteItem(self.listControl, hdelete)
end
hAfter = old_handles[iold + 1]
end
for newItem in new_items[inew + 1:end]
AddItem(self, hparent, newItem)
end
end

function AcceptRoot(self::HierList, root)
DeleteAllItems(self.listControl)
self.itemHandleMap = Dict(commctrl.TVI_ROOT => root)
self.filledItemHandlesMap = Dict(commctrl.TVI_ROOT => root)
subItems = GetSubList(self, root)
AddSubList(self, 0, subItems)
end

function GetBitmapColumn(self::HierList, item)::Int64
if IsExpandable(self, item)
return 0
else
return 4
end
end

function GetSelectedBitmapColumn(self::HierList, item)
return nothing
end

function GetSelectedBitmapColumn(self::HierList, item)::Int64
return 0
end

function CheckChangedChildren(self::HierList)
return CheckChangedChildren(self.listControl)
end

function GetText(self::HierList, item)
return GetItemText(item)
end

function PerformItemSelected(self::HierList, item)
try
SetStatusText(win32ui, "Selected " + GetText(self, item))
catch exn
if exn isa win32ui.error
#= pass =#
end
end
end

function TakeDefaultAction(self::HierList, item)
MessageBox(win32ui, "Got item " + GetText(self, item))
end

mutable struct HierListWithItems <: AbstractHierListWithItems
bitmapID
bitmapMask
listBoxID

            HierListWithItems(root, bitmapID = win32ui.IDB_HIERFOLDERS, listBoxID = nothing, bitmapMask = nothing) = begin
                HierList(root, bitmapID, listBoxID, bitmapMask)
                new(root, bitmapID , listBoxID , bitmapMask )
            end
end
function DelegateCall(self::HierListWithItems, fn)
return fn()
end

function GetBitmapColumn(self::HierListWithItems, item)
rc = DelegateCall(self, item.GetBitmapColumn)
if rc === nothing
rc = GetBitmapColumn(HierList, self)
end
return rc
end

function GetSelectedBitmapColumn(self::HierListWithItems, item)
return DelegateCall(self, item.GetSelectedBitmapColumn)
end

function IsExpandable(self::HierListWithItems, item)
return DelegateCall(self, item.IsExpandable)
end

function GetText(self::HierListWithItems, item)
return DelegateCall(self, item.GetText)
end

function GetSubList(self::HierListWithItems, item)
return DelegateCall(self, item.GetSubList)
end

function PerformItemSelected(self::HierListWithItems, item)
func = (hasfield(typeof(item), :PerformItemSelected) ? 
                getfield(item, :PerformItemSelected) : nothing)
if func === nothing
return PerformItemSelected(HierList, self)
else
return DelegateCall(self, func)
end
end

function TakeDefaultAction(self::HierListWithItems, item)
func = (hasfield(typeof(item), :TakeDefaultAction) ? 
                getfield(item, :TakeDefaultAction) : nothing)
if func === nothing
return TakeDefaultAction(HierList, self)
else
return DelegateCall(self, func)
end
end

mutable struct HierListItem <: AbstractHierListItem


            HierListItem() = begin
                #= pass =#
                new()
            end
end
function GetText(self::HierListItem)
#= pass =#
end

function GetSubList(self::HierListItem)
#= pass =#
end

function IsExpandable(self::HierListItem)
#= pass =#
end

function GetBitmapColumn(self::HierListItem)
return nothing
end

function GetSelectedBitmapColumn(self::HierListItem)
return nothing
end

function __lt__(self::HierListItem, other)::Bool
return id(self) < id(other)
end

function __eq__(self::HierListItem, other)::Bool
return false
end
