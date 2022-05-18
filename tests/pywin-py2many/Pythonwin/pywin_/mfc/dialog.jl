#=  Base class for Dialogs.  Also contains a few useful utility functions
 =#
using PyCall
win32ui = pyimport("win32ui")

import win32con
using win32com_.gen_py.mfc: window
abstract type AbstractDialog <: Abstractwindow.Wnd end
abstract type AbstractPrintDialog <: AbstractDialog end
abstract type AbstractPropertyPage <: AbstractDialog end
abstract type AbstractPropertySheet <: Abstractwindow.Wnd end
abstract type AbstractDlgSimpleInput <: AbstractDlgBaseClass end
function dllFromDll(dllid)
#= given a 'dll' (maybe a dll, filename, etc), return a DLL object =#
if dllid === nothing
return nothing
elseif type_("") == type_(dllid)
return LoadLibrary(win32ui, dllid)
else
try
GetFileName(dllid)
catch exn
if exn isa AttributeError
throw(TypeError("DLL parameter must be None, a filename or a dll object"))
end
end
return dllid
end
end

mutable struct Dialog <: AbstractDialog
#= Base class for a dialog =#
_obj_
bHaveInit
data
dll
dllid

            Dialog(id, dllid = nothing) = begin
                if type_(id) == type_([])
dlg = win32ui.CreateDialogIndirect(id)
else
dlg = win32ui.CreateDialog(id, dll)
end
window.Wnd.__init__(self, dlg)
HookCommands()
                new(id, dllid )
            end
end
function HookCommands(self::Dialog)
#= pass =#
end

function OnAttachedObjectDeath(self::Dialog)
self.data = self._obj_.data
OnAttachedObjectDeath(window.Wnd)
end

function OnOK(self::Dialog)
OnOK(self._obj_)
end

function OnCancel(self::Dialog)
OnCancel(self._obj_)
end

function OnInitDialog(self::Dialog)::Int64
self.bHaveInit = 1
if self._obj_.data
UpdateData(self._obj_, 0)
end
return 1
end

function OnDestroy(self::Dialog, msg)
self.dll = nothing
end

function AddDDX(self::Dialog)
append(self._obj_.datalist, args)
end

function __bool__(self::Dialog)::Bool
return true
end

function __len__(self::Dialog)::Int64
return length(self.data)
end

function __getitem__(self::Dialog, key)
return self.data[key + 1]
end

function __setitem__(self::Dialog, key, item)
self._obj_.data[key + 1] = item
end

function keys(self::Dialog)::Vector
return collect(keys(self.data))
end

function items(self::Dialog)::Vector
return collect(items(self.data))
end

function values(self::Dialog)::Vector
return collect(values(self.data))
end

function has_key(self::Dialog, key)::Bool
return key ∈ self.data
end

mutable struct PrintDialog <: AbstractPrintDialog
#= Base class for a print dialog =#
bHaveInit
dll
pInfo
dllid
flags
parent
printSetupOnly::Int64

            PrintDialog(pInfo, dlgID, printSetupOnly = 0, flags = (((win32ui.PD_ALLPAGES | win32ui.PD_USEDEVMODECOPIES) | win32ui.PD_NOPAGENUMS) | win32ui.PD_HIDEPRINTTOFILE) | win32ui.PD_NOSELECTION, parent = nothing, dllid = nothing) = begin
                if type_(dlgID) == type_([])
throw(TypeError("dlgID parameter must be an integer resource ID"))
end
window.Wnd.__init__(self, dlg)
HookCommands()
                new(pInfo, dlgID, printSetupOnly , flags , parent , dllid )
            end
end
function OnInitDialog(self::PrintDialog)
CreatePrinterDC(self.pInfo)
return OnInitDialog(self._obj_)
end

function OnCancel(self::PrintDialog)
#Delete Unsupported
del(self.pInfo)
end

function OnOK(self::PrintDialog)
#= DoModal has finished. Can now access the users choices =#
OnOK(self._obj_)
pInfo = self.pInfo
flags = GetFlags(pInfo)
self["toFile"] = (flags & win32ui.PD_PRINTTOFILE) != 0
self["direct"] = GetDirect(pInfo)
self["preview"] = GetPreview(pInfo)
self["continuePrinting"] = GetContinuePrinting(pInfo)
self["curPage"] = GetCurPage(pInfo)
self["numPreviewPages"] = GetNumPreviewPages(pInfo)
self["userData"] = GetUserData(pInfo)
self["draw"] = GetDraw(pInfo)
self["pageDesc"] = GetPageDesc(pInfo)
self["minPage"] = GetMinPage(pInfo)
self["maxPage"] = GetMaxPage(pInfo)
self["offsetPage"] = GetOffsetPage(pInfo)
self["fromPage"] = GetFromPage(pInfo)
self["toPage"] = GetToPage(pInfo)
self["copies"] = GetCopies(pInfo)
self["deviceName"] = GetDeviceName(pInfo)
self["driverName"] = GetDriverName(pInfo)
self["printAll"] = PrintAll(pInfo)
self["printCollate"] = PrintCollate(pInfo)
self["printRange"] = PrintRange(pInfo)
self["printSelection"] = PrintSelection(pInfo)
#Delete Unsupported
del(self.pInfo)
end

mutable struct PropertyPage <: AbstractPropertyPage
#= Base class for a Property Page =#
dll
caption::Int64
dllid

            PropertyPage(id, dllid = nothing, caption = 0) = begin
                if dll
oldRes = win32ui.SetResource(dll)
end
if type_(id) == type_([])
dlg = win32ui.CreatePropertyPageIndirect(id)
else
dlg = win32ui.CreatePropertyPage(id, caption)
end
if dll
win32ui.SetResource(oldRes)
end
window.Wnd.__init__(self, dlg)
HookCommands()
                new(id, dllid , caption )
            end
end

mutable struct PropertySheet <: AbstractPropertySheet
dll
sheet
pageList

            PropertySheet(caption, dll = nothing, pageList = nothing) = begin
                window.Wnd.__init__(self, sheet)
if !(pageList === nothing)
AddPage(pageList)
end
                new(caption, dll , pageList )
            end
end
function OnInitDialog(self::PropertySheet)
return OnInitDialog(self._obj_)
end

function DoModal(self::PropertySheet)
if self.dll
oldRes = SetResource(win32ui, self.dll)
end
rc = DoModal(self.sheet)
if self.dll
SetResource(win32ui, oldRes)
end
return rc
end

function AddPage(self::PropertySheet, pages)
if self.dll
oldRes = SetResource(win32ui, self.dll)
end
try
pages[1]
isSeq = 1
catch exn
if exn isa (TypeError, KeyError)
isSeq = 0
end
end
if isSeq != 0
for page in pages
DoAddSinglePage(self, page)
end
else
DoAddSinglePage(self, pages)
end
if self.dll
SetResource(win32ui, oldRes)
end
end

function DoAddSinglePage(self::PropertySheet, page)
#= Page may be page, or int ID. Assumes DLL setup =#
if type_(page) == type_(0)
AddPage(self.sheet, CreatePropertyPage(win32ui, page))
else
AddPage(self.sheet, page)
end
end

function GetSimpleInput(prompt, defValue = "", title = nothing)::DlgSimpleInput
#= displays a dialog, and returns a string, or None if cancelled.
    args prompt, defValue='', title=main frames title =#
if title === nothing
title = GetWindowText(GetMainFrame(win32ui))
end
DlgBaseClass = Dialog
mutable struct DlgSimpleInput <: AbstractDlgSimpleInput
title

            DlgSimpleInput(prompt, defValue, title) = begin
                DlgBaseClass.__init__(self, win32ui.IDD_SIMPLE_INPUT)
AddDDX(win32ui.IDC_EDIT1, "result")
AddDDX(win32ui.IDC_PROMPT1, "prompt")
                new(prompt, defValue, title)
            end
end
function OnInitDialog(self::DlgSimpleInput)
SetWindowText(self, self.title)
return OnInitDialog(DlgBaseClass)
end

dlg = DlgSimpleInput(prompt, defValue, title)
if DoModal(dlg) != win32con.IDOK
return nothing
end
return dlg["result"]
end
