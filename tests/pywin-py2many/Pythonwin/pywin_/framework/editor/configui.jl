using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")

import win32com_.gen_py.scintilla.view
using win32com_.gen_py.mfc: dialog
include("document.jl")

import win32con

using win32com_.gen_py.framework.editor: GetEditorOption, SetEditorOption, DeleteEditorOption, GetEditorFontOption, SetEditorFontOption, defaultCharacterFormat, editorTemplate
import win32com_.gen_py.scintilla.config
abstract type AbstractEditorPropertyPage <: Abstractdialog.PropertyPage end
abstract type AbstractEditorWhitespacePropertyPage <: Abstractdialog.PropertyPage end
paletteVGA = (("Black", 0, 0, 0), ("Navy", 0, 0, 128), ("Green", 0, 128, 0), ("Cyan", 0, 128, 128), ("Maroon", 128, 0, 0), ("Purple", 128, 0, 128), ("Olive", 128, 128, 0), ("Gray", 128, 128, 128), ("Silver", 192, 192, 192), ("Blue", 0, 0, 255), ("Lime", 0, 255, 0), ("Aqua", 0, 255, 255), ("Red", 255, 0, 0), ("Fuchsia", 255, 0, 255), ("Yellow", 255, 255, 0), ("White", 255, 255, 255))
mutable struct EditorPropertyPage <: AbstractEditorPropertyPage
autooptions::Vector
edgeColor
initialEdgeColor
OnButSimple
OnButEdgeColor

            EditorPropertyPage() = begin
                dialog.PropertyPage.__init__(self, win32ui.IDD_PP_EDITOR)
_AddEditorOption(win32ui.IDC_AUTO_RELOAD, "i", "Auto Reload", 1)
_AddEditorOption(win32ui.IDC_COMBO1, "i", "Backup Type", document.BAK_DOT_BAK_BAK_DIR)
_AddEditorOption(win32ui.IDC_AUTOCOMPLETE, "i", "Autocomplete Attributes", 1)
_AddEditorOption(win32ui.IDC_CALLTIPS, "i", "Show Call Tips", 1)
_AddEditorOption(win32ui.IDC_MARGIN_LINENUMBER, "i", "Line Number Margin Width", 0)
_AddEditorOption(win32ui.IDC_RADIO1, "i", "MarkersInMargin", nothing)
_AddEditorOption(win32ui.IDC_MARGIN_MARKER, "i", "Marker Margin Width", nothing)
_AddEditorOption(win32ui.IDC_MARGIN_FOLD, "i", "Fold Margin Width", 12)
_AddEditorOption(win32ui.IDC_FOLD_ENABLE, "i", "Enable Folding", 1)
_AddEditorOption(win32ui.IDC_FOLD_ON_OPEN, "i", "Fold On Open", 0)
_AddEditorOption(win32ui.IDC_FOLD_SHOW_LINES, "i", "Fold Lines", 1)
_AddEditorOption(win32ui.IDC_RIGHTEDGE_ENABLE, "i", "Right Edge Enabled", 0)
_AddEditorOption(win32ui.IDC_RIGHTEDGE_COLUMN, "i", "Right Edge Column", 75)
AddDDX(win32ui.IDC_VSS_INTEGRATE, "bVSS")
AddDDX(win32ui.IDC_KEYBOARD_CONFIG, "Configs", "l")
                new()
            end
end
function _AddEditorOption(self::EditorPropertyPage, idd, typ, optionName, defaultVal)
AddDDX(self, idd, optionName, typ)
if defaultVal != nothing
self[optionName + 1] = GetEditorOption(optionName, defaultVal)
append(self.autooptions, (optionName, defaultVal))
end
end

function OnInitDialog(self::EditorPropertyPage)
for (name, val) in self.autooptions
self[name + 1] = GetEditorOption(name, val)
end
cbo = GetDlgItem(self, win32ui.IDC_COMBO1)
AddString(cbo, "None")
AddString(cbo, ".BAK File")
AddString(cbo, "TEMP dir")
AddString(cbo, "Own dir")
bVSS = GetEditorOption("Source Control Module", "") == "win32com_.gen_py.framework.editor.vss"
self["bVSS"] = bVSS
edit = GetDlgItem(self, win32ui.IDC_RIGHTEDGE_SAMPLE)
SetWindowText(edit, "Sample Color")
rc = OnInitDialog(dialog.PropertyPage)
try
SelectString(GetDlgItem(self, win32ui.IDC_KEYBOARD_CONFIG), -1, GetEditorOption("Keyboard Config", "default"))
catch exn
if exn isa win32ui.error
current_exceptions() != [] ? current_exceptions()[end] : nothing
#= pass =#
end
end
HookCommand(self, self.OnButSimple, win32ui.IDC_FOLD_ENABLE)
HookCommand(self, self.OnButSimple, win32ui.IDC_RADIO1)
HookCommand(self, self.OnButSimple, win32ui.IDC_RADIO2)
HookCommand(self, self.OnButSimple, win32ui.IDC_RIGHTEDGE_ENABLE)
HookCommand(self, self.OnButEdgeColor, win32ui.IDC_RIGHTEDGE_DEFINE)
butMarginEnabled = self["Marker Margin Width"] > 0
SetCheck(GetDlgItem(self, win32ui.IDC_RADIO1), butMarginEnabled)
SetCheck(GetDlgItem(self, win32ui.IDC_RADIO2), !(butMarginEnabled))
self.edgeColor = GetEditorOption("Right Edge Color", RGB(win32api, 239, 239, 239))
self.initialEdgeColor = GetEditorOption("Right Edge Color", RGB(win32api, 239, 239, 239))
for spinner_id in (win32ui.IDC_SPIN1, win32ui.IDC_SPIN2, win32ui.IDC_SPIN3)
spinner = GetDlgItem(self, spinner_id)
SetRange(spinner, 0, 100)
end
UpdateUIForState(self)
return rc
end

function OnButSimple(self::EditorPropertyPage, id, code)
if code == win32con.BN_CLICKED
UpdateUIForState(self)
end
end

function OnButEdgeColor(self::EditorPropertyPage, id, code)
if code == win32con.BN_CLICKED
d = CreateColorDialog(win32ui, self.edgeColor, 0, self)
ccs = [self.edgeColor]
for c in 78:-16:239
push!(ccs, RGB(win32api, c, c, c))
end
SetCustomColors(d, ccs)
if DoModal(d) == win32con.IDOK
self.edgeColor = GetColor(d)
UpdateUIForState(self)
end
end
end

function UpdateUIForState(self::EditorPropertyPage)
folding = GetCheck(GetDlgItem(self, win32ui.IDC_FOLD_ENABLE))
EnableWindow(GetDlgItem(self, win32ui.IDC_FOLD_ON_OPEN), folding)
EnableWindow(GetDlgItem(self, win32ui.IDC_FOLD_SHOW_LINES), folding)
widthEnabled = GetCheck(GetDlgItem(self, win32ui.IDC_RADIO1))
EnableWindow(GetDlgItem(self, win32ui.IDC_MARGIN_MARKER), widthEnabled)
UpdateData(self)
if widthEnabled && self["Marker Margin Width"] == 0
self["Marker Margin Width"] = 16
UpdateData(self, 0)
end
edgeEnabled = GetCheck(GetDlgItem(self, win32ui.IDC_RIGHTEDGE_ENABLE))
EnableWindow(GetDlgItem(self, win32ui.IDC_RIGHTEDGE_COLUMN), edgeEnabled)
EnableWindow(GetDlgItem(self, win32ui.IDC_RIGHTEDGE_SAMPLE), edgeEnabled)
EnableWindow(GetDlgItem(self, win32ui.IDC_RIGHTEDGE_DEFINE), edgeEnabled)
edit = GetDlgItem(self, win32ui.IDC_RIGHTEDGE_SAMPLE)
SetBackgroundColor(edit, 0, self.edgeColor)
end

function OnOK(self::EditorPropertyPage)::Int64
for (name, defVal) in self.autooptions
SetEditorOption(name, self[name + 1])
end
if self["MarkersInMargin"] == 0
SetEditorOption("Marker Margin Width", self["Marker Margin Width"])
else
SetEditorOption("Marker Margin Width", 0)
end
if self.edgeColor != self.initialEdgeColor
SetEditorOption("Right Edge Color", self.edgeColor)
end
if self["bVSS"]
SetEditorOption("Source Control Module", "win32com_.gen_py.framework.editor.vss")
elseif GetEditorOption("Source Control Module", "") == "win32com_.gen_py.framework.editor.vss"
SetEditorOption("Source Control Module", "")
end
configname = GetWindowText(GetDlgItem(self, win32ui.IDC_KEYBOARD_CONFIG))
if configname
if configname == "default"
DeleteEditorOption("Keyboard Config")
else
SetEditorOption("Keyboard Config", configname)
end
LoadConfiguration(win32com_.gen_py.scintilla.view)
end
return 1
end

mutable struct EditorWhitespacePropertyPage <: AbstractEditorWhitespacePropertyPage
autooptions::Vector
cbo
OnButSimple

            EditorWhitespacePropertyPage() = begin
                dialog.PropertyPage.__init__(self, win32ui.IDD_PP_TABS)
_AddEditorOption(win32ui.IDC_TAB_SIZE, "i", "Tab Size", 4)
_AddEditorOption(win32ui.IDC_INDENT_SIZE, "i", "Indent Size", 4)
_AddEditorOption(win32ui.IDC_USE_SMART_TABS, "i", "Smart Tabs", 1)
_AddEditorOption(win32ui.IDC_VIEW_WHITESPACE, "i", "View Whitespace", 0)
_AddEditorOption(win32ui.IDC_VIEW_EOL, "i", "View EOL", 0)
_AddEditorOption(win32ui.IDC_VIEW_INDENTATIONGUIDES, "i", "View Indentation Guides", 0)
                new()
            end
end
function _AddEditorOption(self::EditorWhitespacePropertyPage, idd, typ, optionName, defaultVal)
AddDDX(self, idd, optionName, typ)
self[optionName + 1] = GetEditorOption(optionName, defaultVal)
append(self.autooptions, (optionName, defaultVal))
end

function OnInitDialog(self::EditorWhitespacePropertyPage)
for (name, val) in self.autooptions
self[name + 1] = GetEditorOption(name, val)
end
rc = OnInitDialog(dialog.PropertyPage)
idc = win32ui.IDC_TABTIMMY_NONE
if GetEditorOption("Use Tab Timmy", 1)
idc = win32ui.IDC_TABTIMMY_IND
end
SetCheck(GetDlgItem(self, idc), 1)
idc = win32ui.IDC_RADIO1
if GetEditorOption("Use Tabs", 0)
idc = win32ui.IDC_USE_TABS
end
SetCheck(GetDlgItem(self, idc), 1)
tt_color = GetEditorOption("Tab Timmy Color", RGB(win32api, 255, 0, 0))
self.cbo = GetDlgItem(self, win32ui.IDC_COMBO1)
for c in paletteVGA
AddString(self.cbo, c[1])
end
sel = 0
has_break = false
for c in paletteVGA
if tt_color == RGB(win32api, c[2], c[3], c[4])
has_break = true
break;
end
sel = sel + 1
end
if has_break != true
sel = -1
end
SetCurSel(self.cbo, sel)
HookCommand(self, self.OnButSimple, win32ui.IDC_TABTIMMY_NONE)
HookCommand(self, self.OnButSimple, win32ui.IDC_TABTIMMY_IND)
HookCommand(self, self.OnButSimple, win32ui.IDC_TABTIMMY_BG)
for spinner_id in [win32ui.IDC_SPIN1, win32ui.IDC_SPIN2]
spinner = GetDlgItem(self, spinner_id)
SetRange(spinner, 1, 16)
end
return rc
end

function OnButSimple(self::EditorWhitespacePropertyPage, id, code)
if code == win32con.BN_CLICKED
UpdateUIForState(self)
end
end

function UpdateUIForState(self::EditorWhitespacePropertyPage)
timmy = GetCheck(GetDlgItem(self, win32ui.IDC_TABTIMMY_NONE))
EnableWindow(GetDlgItem(self, win32ui.IDC_COMBO1), !(timmy))
end

function OnOK(self::EditorWhitespacePropertyPage)::Int64
for (name, defVal) in self.autooptions
SetEditorOption(name, self[name + 1])
end
SetEditorOption("Use Tabs", GetCheck(GetDlgItem(self, win32ui.IDC_USE_TABS)))
SetEditorOption("Use Tab Timmy", GetCheck(GetDlgItem(self, win32ui.IDC_TABTIMMY_IND)))
c = paletteVGA[GetCurSel(self.cbo) + 1]
SetEditorOption("Tab Timmy Color", RGB(win32api, c[2], c[3], c[4]))
return 1
end

function testpp()
ps = PropertySheet(dialog, "Editor Options")
AddPage(ps, EditorWhitespacePropertyPage())
DoModal(ps)
end

if abspath(PROGRAM_FILE) == @__FILE__
testpp()
end