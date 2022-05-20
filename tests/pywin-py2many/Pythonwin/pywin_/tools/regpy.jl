using PyCall
win32ui = pyimport("win32ui")

import dialog
import win32con
import commctrl
abstract type AbstractRegistryControl end
abstract type AbstractRegEditPropertyPage <: Abstractdialog.PropertyPage end
abstract type AbstractRegistryPage <: AbstractRegEditPropertyPage end
abstract type AbstractRegistrySheet <: Abstractdialog.PropertySheet end
mutable struct RegistryControl <: AbstractRegistryControl
key
end

mutable struct RegEditPropertyPage <: AbstractRegEditPropertyPage
IDC_LISTVIEW::Int64

                    RegEditPropertyPage(IDC_LISTVIEW::Int64 = 1000) =
                        new(IDC_LISTVIEW)
end
function GetTemplate(self::RegEditPropertyPage)
#= Return the template used to create this dialog =#
w = 152
h = 122
SS_STD = win32con.WS_CHILD | win32con.WS_VISIBLE
FRAMEDLG_STD = win32con.WS_CAPTION | win32con.WS_SYSMENU
style = ((FRAMEDLG_STD | win32con.WS_VISIBLE) | win32con.DS_SETFONT) | win32con.WS_MINIMIZEBOX
template = [[self.caption, (0, 0, w, h), style, nothing, (8, "Helv")]]
lvStyle = (((((SS_STD | commctrl.LVS_EDITLABELS) | commctrl.LVS_REPORT) | commctrl.LVS_AUTOARRANGE) | commctrl.LVS_ALIGNLEFT) | win32con.WS_BORDER) | win32con.WS_TABSTOP
push!(template, ["SysListView32", "", self.IDC_LISTVIEW, (10, 10, 185, 100), lvStyle])
return template
end

mutable struct RegistryPage <: AbstractRegistryPage
caption::String
listview

            RegistryPage() = begin
                RegEditPropertyPage(GetTemplate())
                new()
            end
end
function OnInitDialog(self::RegistryPage)
self.listview = GetDlgItem(self, self.IDC_LISTVIEW)
OnInitDialog(RegEditPropertyPage, self)
itemDetails = (commctrl.LVCFMT_LEFT, 100, "App", 0)
InsertColumn(self.listview, 0, itemDetails)
itemDetails = (commctrl.LVCFMT_LEFT, 1024, "Paths", 0)
InsertColumn(self.listview, 1, itemDetails)
index = InsertItem(self.listview, 0, "App")
SetItemText(self.listview, index, 1, "Path")
end

mutable struct RegistrySheet <: AbstractRegistrySheet


            RegistrySheet(title) = begin
                dialog.PropertySheet.__init__(self, title)
HookMessage(OnActivate, win32con.WM_ACTIVATE)
                new(title)
            end
end
function OnActivate(self::RegistrySheet, msg)
println("OnAcivate")
end

function t()
ps = RegistrySheet("Registry Settings")
AddPage(ps, RegistryPage())
DoModal(ps)
end

if abspath(PROGRAM_FILE) == @__FILE__
t()
end