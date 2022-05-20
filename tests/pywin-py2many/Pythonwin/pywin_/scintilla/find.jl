using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32con

using win32com_.gen_py.mfc: dialog
import afxres
using win32com_.gen_py.framework: scriptutils
abstract type AbstractSearchParams end
abstract type AbstractFindReplaceDialog <: Abstractdialog.Dialog end
abstract type AbstractFindDialog <: AbstractFindReplaceDialog end
abstract type AbstractReplaceDialog <: AbstractFindReplaceDialog end
FOUND_NOTHING = 0
FOUND_NORMAL = 1
FOUND_LOOPED_BACK = 2
FOUND_NEXT_FILE = 3
mutable struct SearchParams <: AbstractSearchParams
other

            SearchParams(other = nothing) = begin
                if other === nothing
__dict__["findText"] = ""
__dict__["replaceText"] = ""
__dict__["matchCase"] = 0
__dict__["matchWords"] = 0
__dict__["acrossFiles"] = 0
__dict__["remember"] = 1
__dict__["sel"] = (-1, -1)
__dict__["keepDialogOpen"] = 0
else
__dict__.update(other.__dict__)
end
                new(other )
            end
end
function __setattr__(self::SearchParams, attr, val)
if !hasfield(typeof(self), :attr)
throw(AttributeError(attr))
end
self.__dict__[attr] = val
end

curDialog = nothing
lastSearch = SearchParams()
defaultSearch = SearchParams()
searchHistory = []
function ShowFindDialog()
_ShowDialog(FindDialog)
end

function ShowReplaceDialog()
_ShowDialog(ReplaceDialog)
end

function _ShowDialog(dlgClass)
global curDialog
if curDialog != nothing
if curDialog.__class__ != dlgClass
DestroyWindow(curDialog)
curDialog = nothing
else
SetFocus(curDialog)
end
end
if curDialog === nothing
curDialog = dlgClass()
CreateWindow(curDialog)
end
end

function FindNext()::Int64
params = SearchParams(lastSearch)
params.sel = (-1, -1)
if !(params.findText)
ShowFindDialog()
else
return _FindIt(nothing, params)
end
end

function _GetControl(control = nothing)
if control === nothing
control = GetActiveEditControl(scriptutils)
end
return control
end

function _FindIt(control, searchParams)::Int64
global lastSearch, defaultSearch
control = _GetControl(control)
if control === nothing
return FOUND_NOTHING
end
flags = 0
if searchParams.matchWords
flags = flags | win32con.FR_WHOLEWORD
end
if searchParams.matchCase
flags = flags | win32con.FR_MATCHCASE
end
if searchParams.sel == (-1, -1)
sel = GetSel(control)
if sel == lastSearch.sel
sel = (sel[1] + 1, sel[1] + 1)
end
else
sel = searchParams.sel
end
if sel[1] == sel[2]
sel = (sel[1], GetTextLength(control))
end
rc = FOUND_NOTHING
posFind, foundSel = FindText(control, flags, sel, searchParams.findText)
lastSearch = SearchParams(searchParams)
if posFind >= 0
rc = FOUND_NORMAL
lineno = LineFromChar(control, posFind)
SCIEnsureVisible(control, lineno)
SetSel(control, foundSel)
SetFocus(control)
SetStatusText(win32ui, LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE))
end
if rc == FOUND_NOTHING && lastSearch.acrossFiles
try
try
doc = GetDocument(control)
catch exn
if exn isa AttributeError
try
doc = GetDocument(GetParent(control))
catch exn
if exn isa AttributeError
println("Cant find a document for the control!")
doc = nothing
end
end
end
end
if doc != nothing
template = GetDocTemplate(doc)
alldocs = GetDocumentList(template)
mypos = index(alldocs, doc)
lookpos = index(alldocs, doc)
while true
lookpos = (lookpos + 1) % length(alldocs)
if lookpos == mypos
has_break = true
break;
end
view = GetFirstView(alldocs[lookpos + 1])
posFind, foundSel = FindText(view, flags, (0, GetTextLength(view)), searchParams.findText)
if posFind >= 0
nChars = foundSel[2] - foundSel[1]
lineNo = LineFromChar(view, posFind)
lineStart = LineIndex(view, lineNo)
colNo = posFind - lineStart
JumpToDocument(scriptutils, GetPathName(alldocs[lookpos + 1]), lineNo + 1, colNo + 1, nChars)
rc = FOUND_NEXT_FILE
has_break = true
break;
end
end
end
catch exn
if exn isa win32ui.error
#= pass =#
end
end
end
if rc == FOUND_NOTHING
posFind, foundSel = FindText(control, flags, (0, sel[1] - 1), searchParams.findText)
if posFind >= 0
SCIEnsureVisible(control, LineFromChar(control, foundSel[1]))
SetSel(control, foundSel)
SetFocus(control)
SetStatusText(win32ui, "Not found! Searching from the top of the file.")
rc = FOUND_LOOPED_BACK
else
lastSearch.sel = (-1, -1)
SetStatusText(win32ui, "Can not find \'%s\'" % searchParams.findText)
end
end
if rc != FOUND_NOTHING
lastSearch.sel = foundSel
end
if lastSearch.remember
defaultSearch = lastSearch
try
ix = findfirst(isequal(searchParams.findText), searchHistory)
catch exn
if exn isa ValueError
if length(searchHistory) > 50
searchHistory[51:end] = []
end
end
end
insert(searchHistory, 0, searchParams.findText)
end
return rc
end

function _ReplaceIt(control)::Int64
control = _GetControl(control)
statusText = "Can not find \'%s\'." % lastSearch.findText
rc = FOUND_NOTHING
if control != nothing && lastSearch.sel != (-1, -1)
ReplaceSel(control, lastSearch.replaceText)
rc = FindNext()
if rc != FOUND_NOTHING
statusText = LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE)
end
end
SetStatusText(win32ui, statusText)
return rc
end

mutable struct FindReplaceDialog <: AbstractFindReplaceDialog
editFindText
butMatchWords
butMatchCase
butKeepDialogOpen
butAcrossFiles
butRemember

            FindReplaceDialog() = begin
                dialog.Dialog.__init__(self, _GetDialogTemplate())
HookCommand(OnFindNext, 109)
                new()
            end
end
function OnInitDialog(self::FindReplaceDialog)
self.editFindText = GetDlgItem(self, 102)
self.butMatchWords = GetDlgItem(self, 105)
self.butMatchCase = GetDlgItem(self, 107)
self.butKeepDialogOpen = GetDlgItem(self, 115)
self.butAcrossFiles = GetDlgItem(self, 116)
self.butRemember = GetDlgItem(self, 117)
SetWindowText(self.editFindText, defaultSearch.findText)
control = _GetControl()
if control
sel = GetSelText(control)
if length(sel) != 0
SetWindowText(self.editFindText, sel)
if defaultSearch.remember
defaultSearch.findText = sel
end
end
end
for hist in searchHistory
AddString(self.editFindText, hist)
end
if hasfield(typeof(self.editFindText), :SetEditSel)
SetEditSel(self.editFindText, 0, -2)
else
SetSel(self.editFindText, 0, -2)
end
SetFocus(self.editFindText)
SetCheck(self.butMatchWords, defaultSearch.matchWords)
SetCheck(self.butMatchCase, defaultSearch.matchCase)
SetCheck(self.butKeepDialogOpen, defaultSearch.keepDialogOpen)
SetCheck(self.butAcrossFiles, defaultSearch.acrossFiles)
SetCheck(self.butRemember, defaultSearch.remember)
return OnInitDialog(dialog.Dialog)
end

function OnDestroy(self::FindReplaceDialog, msg)
global curDialog
curDialog = nothing
return OnDestroy(dialog.Dialog, self)
end

function DoFindNext(self::FindReplaceDialog)::Int64
params = SearchParams()
params.findText = GetWindowText(self.editFindText)
params.matchCase = GetCheck(self.butMatchCase)
params.matchWords = GetCheck(self.butMatchWords)
params.acrossFiles = GetCheck(self.butAcrossFiles)
params.remember = GetCheck(self.butRemember)
return _FindIt(nothing, params)
end

function OnFindNext(self::FindReplaceDialog, id, code)
if !GetWindowText(self.editFindText)
MessageBeep(win32api)
return
end
if DoFindNext(self) != FOUND_NOTHING
if !GetCheck(self.butKeepDialogOpen)
DestroyWindow(self)
end
end
end

mutable struct FindDialog <: AbstractFindDialog

end
function _GetDialogTemplate(self::FindDialog)
style = ((((win32con.DS_MODALFRAME | win32con.WS_POPUP) | win32con.WS_VISIBLE) | win32con.WS_CAPTION) | win32con.WS_SYSMENU) | win32con.DS_SETFONT
visible = win32con.WS_CHILD | win32con.WS_VISIBLE
dt = [["Find", (0, 2, 240, 75), style, nothing, (8, "MS Sans Serif")], ["Static", "Fi&nd What:", 101, (5, 8, 40, 10), visible], ["ComboBox", "", 102, (50, 7, 120, 120), ((((visible | win32con.WS_BORDER) | win32con.WS_TABSTOP) | win32con.WS_VSCROLL) | win32con.CBS_DROPDOWN) | win32con.CBS_AUTOHSCROLL], ["Button", "Match &whole word only", 105, (5, 23, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Match &case", 107, (5, 33, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Keep &dialog open", 115, (5, 43, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Across &open files", 116, (5, 52, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "&Remember as default search", 117, (5, 61, 150, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "&Find Next", 109, (185, 5, 50, 14), (visible | win32con.BS_DEFPUSHBUTTON) | win32con.WS_TABSTOP], ["Button", "Cancel", win32con.IDCANCEL, (185, 23, 50, 14), visible | win32con.WS_TABSTOP]]
return dt
end

mutable struct ReplaceDialog <: AbstractReplaceDialog
editReplaceText
butReplace
butReplaceAll
OnReplace
OnReplaceAll
OnActivate
end
function _GetDialogTemplate(self::ReplaceDialog)
style = ((((win32con.DS_MODALFRAME | win32con.WS_POPUP) | win32con.WS_VISIBLE) | win32con.WS_CAPTION) | win32con.WS_SYSMENU) | win32con.DS_SETFONT
visible = win32con.WS_CHILD | win32con.WS_VISIBLE
dt = [["Replace", (0, 2, 240, 95), style, 0, (8, "MS Sans Serif")], ["Static", "Fi&nd What:", 101, (5, 8, 40, 10), visible], ["ComboBox", "", 102, (60, 7, 110, 120), ((((visible | win32con.WS_BORDER) | win32con.WS_TABSTOP) | win32con.WS_VSCROLL) | win32con.CBS_DROPDOWN) | win32con.CBS_AUTOHSCROLL], ["Static", "Re&place with:", 103, (5, 25, 50, 10), visible], ["ComboBox", "", 104, (60, 24, 110, 120), ((((visible | win32con.WS_BORDER) | win32con.WS_TABSTOP) | win32con.WS_VSCROLL) | win32con.CBS_DROPDOWN) | win32con.CBS_AUTOHSCROLL], ["Button", "Match &whole word only", 105, (5, 42, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Match &case", 107, (5, 52, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Keep &dialog open", 115, (5, 62, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "Across &open files", 116, (5, 72, 100, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "&Remember as default search", 117, (5, 81, 150, 10), (visible | win32con.BS_AUTOCHECKBOX) | win32con.WS_TABSTOP], ["Button", "&Find Next", 109, (185, 5, 50, 14), (visible | win32con.BS_DEFPUSHBUTTON) | win32con.WS_TABSTOP], ["Button", "&Replace", 110, (185, 23, 50, 14), visible | win32con.WS_TABSTOP], ["Button", "Replace &All", 111, (185, 41, 50, 14), visible | win32con.WS_TABSTOP], ["Button", "Cancel", win32con.IDCANCEL, (185, 59, 50, 14), visible | win32con.WS_TABSTOP]]
return dt
end

function OnInitDialog(self::ReplaceDialog)
rc = OnInitDialog(FindReplaceDialog)
HookCommand(self, self.OnReplace, 110)
HookCommand(self, self.OnReplaceAll, 111)
HookMessage(self, self.OnActivate, win32con.WM_ACTIVATE)
self.editReplaceText = GetDlgItem(self, 104)
SetWindowText(self.editReplaceText, lastSearch.replaceText)
if hasfield(typeof(self.editReplaceText), :SetEditSel)
SetEditSel(self.editReplaceText, 0, -2)
else
SetSel(self.editReplaceText, 0, -2)
end
self.butReplace = GetDlgItem(self, 110)
self.butReplaceAll = GetDlgItem(self, 111)
CheckButtonStates(self)
return rc
end

function CheckButtonStates(self::ReplaceDialog)
ft = GetWindowText(self.editFindText)
control = _GetControl()
bCanReplace = control != nothing && lastSearch.sel == GetSel(control)
EnableWindow(self.butReplace, bCanReplace)
end

function OnActivate(self::ReplaceDialog, msg)
wparam = msg[3]
fActive = LOWORD(win32api, wparam)
if fActive != win32con.WA_INACTIVE
CheckButtonStates(self)
end
end

function OnFindNext(self::ReplaceDialog, id, code)
DoFindNext(self)
CheckButtonStates(self)
end

function OnReplace(self::ReplaceDialog, id, code)
lastSearch.replaceText = GetWindowText(self.editReplaceText)
_ReplaceIt(nothing)
end

function OnReplaceAll(self::ReplaceDialog, id, code)
control = _GetControl(nothing)
if control != nothing
SetSel(control, 0)
num = 0
if DoFindNext(self) == FOUND_NORMAL
num = 1
lastSearch.replaceText = GetWindowText(self.editReplaceText)
while _ReplaceIt(control) == FOUND_NORMAL
num = num + 1
end
end
SetStatusText(win32ui, "Replaced %d occurrences" % num)
if num > 0 && !GetCheck(self.butKeepDialogOpen)
DestroyWindow(self)
end
end
end

if abspath(PROGRAM_FILE) == @__FILE__
ShowFindDialog()
end