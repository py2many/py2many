using Printf
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")



import win32con

include("app.jl")

import string
tools = Dict()
idPos = 100
abstract type AbstractToolMenuPropPage <: Abstractdialog.PropertyPage end
defaultToolMenuItems = [("Browser", "win32ui.GetApp().OnViewBrowse(0,0)"), ("Browse PythonPath", "from win32com_.gen_py.tools import browseProjects;browseProjects.Browse()"), ("Edit Python Path", "from win32com_.gen_py.tools import regedit;regedit.EditRegistry()"), ("COM Makepy utility", "from win32com_.client import makepy;makepy.main()"), ("COM Browser", "from win32com_.client import combrowse;combrowse.main()"), ("Trace Collector Debugging tool", "from win32com_.gen_py.tools import TraceCollector;TraceCollector.MakeOutputWindow()")]
function LoadToolMenuItems()::Vector
items = []
lookNo = 1
while true
menu = GetProfileVal(win32ui, "Tools Menu\\%s" % lookNo, "", "")
if menu == ""
has_break = true
break;
end
cmd = GetProfileVal(win32ui, "Tools Menu\\%s" % lookNo, "Command", "")
push!(items, (menu, cmd))
lookNo = lookNo + 1
end
if length(items) == 0
items = defaultToolMenuItems
end
return items
end

function WriteToolMenuItems(items)
try
mainKey = GetAppRegistryKey(win32ui)
toolKey = RegOpenKey(win32api, mainKey, "Tools Menu")
catch exn
if exn isa win32ui.error
toolKey = nothing
end
end
if toolKey != nothing
while true
try
subkey = RegEnumKey(win32api, toolKey, 0)
catch exn
if exn isa win32api.error
break;
end
end
RegDeleteKey(win32api, toolKey, subkey)
end
end
if items == defaultToolMenuItems
return
end
itemNo = 1
for (menu, cmd) in items
WriteProfileVal(win32ui, "Tools Menu\\%s" % itemNo, "", menu)
WriteProfileVal(win32ui, "Tools Menu\\%s" % itemNo, "Command", cmd)
itemNo = itemNo + 1
end
end

function SetToolsMenu(menu, menuPos = nothing)
global tools
global idPos
toolsMenu = CreatePopupMenu(win32ui)
items = LoadToolMenuItems()
for (menuString, cmd) in items
tools[idPos] = (menuString, cmd, menuString)
AppendMenu(toolsMenu, win32con.MF_ENABLED | win32con.MF_STRING, idPos, menuString)
HookCommand(GetMainFrame(win32ui), HandleToolCommand, idPos)
idPos = idPos + 1
end
if menuPos === nothing
menuPos = GetMenuItemCount(menu) - 2
if menuPos < 0
menuPos = 0
end
end
InsertMenu(menu, menuPos, ((win32con.MF_BYPOSITION | win32con.MF_ENABLED) | win32con.MF_STRING) | win32con.MF_POPUP, GetHandle(toolsMenu), "&Tools")
end

function HandleToolCommand(cmd, code)
global tools
menuString, pyCmd, desc = tools[cmd]
SetStatusText(win32ui, "Executing tool %s" % desc, 1)
pyCmd = replace(pyCmd, Regex("\\\\n") => s"\n")
DoWaitCursor(win32ui, 1)
oldFlag = nothing
try
oldFlag = sys.stdout.template.writeQueueing
sys.stdout.template.writeQueueing = 0
catch exn
if exn isa (NameError, AttributeError)
#= pass =#
end
end
try
exec("%s\n" % pyCmd)
worked = 1
catch exn
if exn isa SystemExit
worked = 1
end
@printf("Failed to execute command:\n%s\n", pyCmd)
current_exceptions() != [] ? current_exceptions()[end] : nothing
worked = 0
end
if oldFlag != nothing
sys.stdout.template.writeQueueing = oldFlag
end
DoWaitCursor(win32ui, 0)
if worked != 0
text = "Completed successfully."
else
text = "Error executing %s." % desc
end
SetStatusText(win32ui, text, 1)
end

import commctrl
using win32com_.gen_py.mfc: dialog
if win32ui.UNICODE
LVN_ENDLABELEDIT = commctrl.LVN_ENDLABELEDITW
else
LVN_ENDLABELEDIT = commctrl.LVN_ENDLABELEDITA
end
mutable struct ToolMenuPropPage <: AbstractToolMenuPropPage
bImChangingEditControls::Int64
editMenuCommand
butNew
listControl
OnCommandEditControls
OnNotifyListControl
OnNotifyListControlEndLabelEdit
OnButtonNew
OnButtonDelete
OnButtonMove

            ToolMenuPropPage() = begin
                dialog.PropertyPage.__init__(self, win32ui.IDD_PP_TOOLMENU)
                new()
            end
end
function OnInitDialog(self::ToolMenuPropPage)
self.editMenuCommand = GetDlgItem(self, win32ui.IDC_EDIT2)
self.butNew = GetDlgItem(self, win32ui.IDC_BUTTON3)
HookCommand(self, self.OnCommandEditControls, win32ui.IDC_EDIT1)
HookCommand(self, self.OnCommandEditControls, win32ui.IDC_EDIT2)
HookNotify(self, self.OnNotifyListControl, commctrl.LVN_ITEMCHANGED)
HookNotify(self, self.OnNotifyListControlEndLabelEdit, commctrl.LVN_ENDLABELEDIT)
HookCommand(self, self.OnButtonNew, win32ui.IDC_BUTTON3)
HookCommand(self, self.OnButtonDelete, win32ui.IDC_BUTTON4)
HookCommand(self, self.OnButtonMove, win32ui.IDC_BUTTON1)
HookCommand(self, self.OnButtonMove, win32ui.IDC_BUTTON2)
lc = GetDlgItem(self, win32ui.IDC_LIST1)
rect = GetWindowRect(lc)
cx = rect[3] - rect[1]
colSize = ((cx / 2) - GetSystemMetrics(win32api, win32con.SM_CXBORDER)) - 1
item = (commctrl.LVCFMT_LEFT, colSize, "Menu Text")
InsertColumn(lc, 0, item)
item = (commctrl.LVCFMT_LEFT, colSize, "Python Command")
InsertColumn(lc, 1, item)
itemNo = 0
for (desc, cmd) in LoadToolMenuItems()
InsertItem(lc, itemNo, desc)
SetItemText(lc, itemNo, 1, cmd)
itemNo = itemNo + 1
end
self.listControl = lc
return OnInitDialog(dialog.PropertyPage)
end

function OnOK(self::ToolMenuPropPage)
items = []
itemLook = 0
while true
try
text = GetItemText(self.listControl, itemLook, 0)
if !(text)
has_break = true
break;
end
push!(items, (text, GetItemText(self.listControl, itemLook, 1)))
catch exn
if exn isa win32ui.error
break;
end
end
itemLook = itemLook + 1
end
WriteToolMenuItems(items)
return OnOK(self._obj_)
end

function OnCommandEditControls(self::ToolMenuPropPage, id, cmd)::Int64
if cmd == win32con.EN_CHANGE && !(self.bImChangingEditControls)
itemNo = GetNextItem(self.listControl, -1, commctrl.LVNI_SELECTED)
newText = GetWindowText(self.editMenuCommand)
SetItemText(self.listControl, itemNo, 1, newText)
end
return 0
end

function OnNotifyListControlEndLabelEdit(self::ToolMenuPropPage, id, cmd)
newText = GetWindowText(GetEditControl(self.listControl))
itemNo = GetNextItem(self.listControl, -1, commctrl.LVNI_SELECTED)
SetItemText(self.listControl, itemNo, 0, newText)
end

function OnNotifyListControl(self::ToolMenuPropPage, id, cmd)::Int64
try
itemNo = GetNextItem(self.listControl, -1, commctrl.LVNI_SELECTED)
catch exn
if exn isa win32ui.error
return
end
end
self.bImChangingEditControls = 1
try
item = GetItem(self.listControl, itemNo, 1)
SetWindowText(self.editMenuCommand, item[5])
finally
self.bImChangingEditControls = 0
end
return 0
end

function OnButtonNew(self::ToolMenuPropPage, id, cmd)
if cmd == win32con.BN_CLICKED
newIndex = GetItemCount(self.listControl)
InsertItem(self.listControl, newIndex, "Click to edit the text")
EnsureVisible(self.listControl, newIndex, 0)
end
end

function OnButtonMove(self::ToolMenuPropPage, id, cmd)
if cmd == win32con.BN_CLICKED
try
itemNo = GetNextItem(self.listControl, -1, commctrl.LVNI_SELECTED)
catch exn
if exn isa win32ui.error
return
end
end
menu = GetItemText(self.listControl, itemNo, 0)
cmd = GetItemText(self.listControl, itemNo, 1)
if id == win32ui.IDC_BUTTON1
if itemNo > 0
DeleteItem(self.listControl, itemNo)
InsertItem(self.listControl, itemNo - 1, menu)
SetItemText(self.listControl, itemNo - 1, 1, cmd)
end
elseif itemNo < (GetItemCount(self.listControl) - 1)
DeleteItem(self.listControl, itemNo)
InsertItem(self.listControl, itemNo + 1, menu)
SetItemText(self.listControl, itemNo + 1, 1, cmd)
end
end
end

function OnButtonDelete(self::ToolMenuPropPage, id, cmd)
if cmd == win32con.BN_CLICKED
try
itemNo = GetNextItem(self.listControl, -1, commctrl.LVNI_SELECTED)
catch exn
if exn isa win32ui.error
return
end
end
DeleteItem(self.listControl, itemNo)
end
end
