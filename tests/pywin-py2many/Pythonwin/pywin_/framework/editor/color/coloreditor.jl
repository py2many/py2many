using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.debugger
import win32com_.gen_py.framework.interact
using win32com_.gen_py.scintilla: configui

import win32con


import win32com_.gen_py.scintilla.keycodes
using win32com_.gen_py.scintilla: bindings
using win32com_.gen_py.framework.editor: GetEditorOption, SetEditorOption, GetEditorFontOption, SetEditorFontOption, defaultCharacterFormat
MSG_CHECK_EXTERNAL_FILE = win32con.WM_USER + 1999
MARKER_BOOKMARK = 0
MARKER_BREAKPOINT = 1
MARKER_CURRENT = 2
using win32com_.gen_py.debugger: dbgcon
using win32com_.gen_py.scintilla.document: CScintillaDocument
using win32com_.gen_py.framework.editor.document: EditorDocumentBase
abstract type AbstractSyntEditDocument <: AbstractEditorDocumentBase end
abstract type AbstractSyntEditView <: AbstractSyntEditViewParent end
abstract type AbstractSplitterFrame <: AbstractEditorFrame end
abstract type AbstractSyntEditTemplate <: AbstractEditorTemplateBase end
using win32com_.gen_py.scintilla: scintillacon
import win32com_.gen_py.scintilla.view
mutable struct SyntEditDocument <: AbstractSyntEditDocument
#= A SyntEdit document. =#

end
function OnDebuggerStateChange(self::SyntEditDocument, state)
_ApplyOptionalToViews(self, "OnDebuggerStateChange", state)
end

function HookViewNotifications(self::SyntEditDocument, view)
HookViewNotifications(EditorDocumentBase, self, view)
SCISetUndoCollection(view, 1)
end

function FinalizeViewCreation(self::SyntEditDocument, view)
FinalizeViewCreation(EditorDocumentBase, self, view)
if view == GetFirstView(self)
CheckIDLEMenus(GetDocTemplate(self), view.idle)
end
end

SyntEditViewParent = win32com_.gen_py.scintilla.view.CScintillaView
mutable struct SyntEditView <: AbstractSyntEditView
#= A view of a SyntEdit.  Obtains data from document. =#
bCheckingFile::Int64
bFolding
OnRClick
OnCmdViewFold
OnUpdateViewFold
OnCmdViewFoldTopLevel
OnCheckExternalDocumentUpdated
OnSetFocus

            SyntEditView(doc) = begin
                SyntEditViewParent.__init__(self, doc)
                new(doc)
            end
end
function OnInitialUpdate(self::SyntEditView)
OnInitialUpdate(SyntEditViewParent)
HookMessage(self, self.OnRClick, win32con.WM_RBUTTONDOWN)
for id in [win32ui.ID_VIEW_FOLD_COLLAPSE, win32ui.ID_VIEW_FOLD_COLLAPSE_ALL, win32ui.ID_VIEW_FOLD_EXPAND, win32ui.ID_VIEW_FOLD_EXPAND_ALL]
HookCommand(self, self.OnCmdViewFold, id)
HookCommandUpdate(self, self.OnUpdateViewFold, id)
end
HookCommand(self, self.OnCmdViewFoldTopLevel, win32ui.ID_VIEW_FOLD_TOPLEVEL)
SCIMarkerDefineAll(self, MARKER_BOOKMARK, scintillacon.SC_MARK_ROUNDRECT, RGB(win32api, 0, 0, 0), RGB(win32api, 0, 255, 255))
SCIMarkerDefine(self, MARKER_CURRENT, scintillacon.SC_MARK_ARROW)
SCIMarkerSetBack(self, MARKER_CURRENT, RGB(win32api, 255, 255, 0))
if true
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEROPEN, scintillacon.SC_MARK_MINUS, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDER, scintillacon.SC_MARK_PLUS, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERSUB, scintillacon.SC_MARK_EMPTY, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERTAIL, scintillacon.SC_MARK_EMPTY, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEREND, scintillacon.SC_MARK_EMPTY, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEROPENMID, scintillacon.SC_MARK_EMPTY, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERMIDTAIL, scintillacon.SC_MARK_EMPTY, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
else
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEROPEN, scintillacon.SC_MARK_CIRCLEMINUS, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDER, scintillacon.SC_MARK_CIRCLEPLUS, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERSUB, scintillacon.SC_MARK_VLINE, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERTAIL, scintillacon.SC_MARK_LCORNERCURVE, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEREND, scintillacon.SC_MARK_CIRCLEPLUSCONNECTED, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDEROPENMID, scintillacon.SC_MARK_CIRCLEMINUSCONNECTED, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
SCIMarkerDefineAll(self, scintillacon.SC_MARKNUM_FOLDERMIDTAIL, scintillacon.SC_MARK_TCORNERCURVE, RGB(win32api, 255, 255, 255), RGB(win32api, 0, 0, 0))
end
SCIMarkerDefine(self, MARKER_BREAKPOINT, scintillacon.SC_MARK_CIRCLE)
SCIMarkerSetFore(self, MARKER_BREAKPOINT, RGB(win32api, 0, 0, 0))
try
if win32com_.gen_py.debugger.currentDebugger === nothing
state = dbgcon.DBGSTATE_NOT_DEBUGGING
else
state = win32com_.gen_py.debugger.currentDebugger.debuggerState
end
catch exn
if exn isa ImportError
state = dbgcon.DBGSTATE_NOT_DEBUGGING
end
end
OnDebuggerStateChange(self, state)
end

function _GetSubConfigNames(self::SyntEditView)
return ["editor"]
end

function DoConfigChange(self::SyntEditView)
DoConfigChange(SyntEditViewParent)
tabSize = GetEditorOption("Tab Size", 4, 2)
indentSize = GetEditorOption("Indent Size", 4, 2)
bUseTabs = GetEditorOption("Use Tabs", 0)
bSmartTabs = GetEditorOption("Smart Tabs", 1)
ext = IDLEExtension(self.idle, "AutoIndent")
SCISetViewWS(self, GetEditorOption("View Whitespace", 0))
SCISetViewEOL(self, GetEditorOption("View EOL", 0))
SCISetIndentationGuides(self, GetEditorOption("View Indentation Guides", 0))
if GetEditorOption("Right Edge Enabled", 0)
mode = scintillacon.EDGE_BACKGROUND
else
mode = scintillacon.EDGE_NONE
end
SCISetEdgeMode(self, mode)
SCISetEdgeColumn(self, GetEditorOption("Right Edge Column", 75))
SCISetEdgeColor(self, GetEditorOption("Right Edge Color", RGB(win32api, 239, 239, 239)))
width = GetEditorOption("Marker Margin Width", 16)
SCISetMarginWidthN(self, 1, width)
width = GetEditorOption("Fold Margin Width", 12)
SCISetMarginWidthN(self, 2, width)
width = GetEditorOption("Line Number Margin Width", 0)
SCISetMarginWidthN(self, 0, width)
self.bFolding = GetEditorOption("Enable Folding", 1)
fold_flags = 0
SendScintilla(self, scintillacon.SCI_SETMODEVENTMASK, scintillacon.SC_MOD_CHANGEFOLD)
if self.bFolding
if GetEditorOption("Fold Lines", 1)
fold_flags = 16
end
end
SCISetProperty(self, "fold", self.bFolding)
SCISetFoldFlags(self, fold_flags)
tt_color = GetEditorOption("Tab Timmy Color", RGB(win32api, 255, 0, 0))
SendScintilla(self, scintillacon.SCI_INDICSETFORE, 1, tt_color)
tt_use = GetEditorOption("Use Tab Timmy", 1)
if tt_use
SCISetProperty(self, "tab.timmy.whinge.level", "1")
end
if bSmartTabs
config(ext, 1, 5, 4)
set_indentation_params(ext, 1)
if ext.indentwidth == 5
usetabs = 1
indentwidth = tabSize
elseif GetTextLength(self) == 0
usetabs = bUseTabs
indentwidth = indentSize
else
indentwidth = ext.indentwidth
usetabs = 0
end
config(ext, usetabs, indentwidth, tabSize)
else
config(ext, bUseTabs, tabSize, indentSize)
end
SCISetIndent(self, indentSize)
SCISetTabWidth(self, tabSize)
end

function OnDebuggerStateChange(self::SyntEditView, state)
if state == dbgcon.DBGSTATE_NOT_DEBUGGING
SCIMarkerSetBack(self, MARKER_BREAKPOINT, RGB(win32api, 239, 239, 239))
else
SCIMarkerSetBack(self, MARKER_BREAKPOINT, RGB(win32api, 255, 128, 128))
end
end

function HookDocumentHandlers(self::SyntEditView)
HookDocumentHandlers(SyntEditViewParent)
HookMessage(self, self.OnCheckExternalDocumentUpdated, MSG_CHECK_EXTERNAL_FILE)
end

function HookHandlers(self::SyntEditView)
HookHandlers(SyntEditViewParent)
HookMessage(self, self.OnSetFocus, win32con.WM_SETFOCUS)
end

function _PrepareUserStateChange(self::SyntEditView)::Tuple
return (GetSel(self), GetFirstVisibleLine(self))
end

function _EndUserStateChange(self::SyntEditView, info)
scrollOff = info[2] - GetFirstVisibleLine(self)
if scrollOff
LineScroll(self, scrollOff)
end
max = GetTextLength(self)
newPos = (min(info[1][1], max), min(info[1][2], max))
SetSel(self, newPos)
end

function OnMarginClick(self::SyntEditView, std, extra)::Int64
notify = SCIUnpackNotifyMessage(self, extra)
if notify.margin == 2
line_click = LineFromChar(self, notify.position)
if SCIGetFoldLevel(self, line_click) & scintillacon.SC_FOLDLEVELHEADERFLAG
SCIToggleFold(self, line_click)
end
end
return 1
end

function OnSetFocus(self::SyntEditView, msg)::Int64
OnCheckExternalDocumentUpdated(self, msg)
return 1
end

function OnCheckExternalDocumentUpdated(self::SyntEditView, msg)
if self.bCheckingFile != 0
return
end
self.bCheckingFile = 1
CheckExternalDocumentUpdated(GetDocument(self))
self.bCheckingFile = 0
end

function OnRClick(self::SyntEditView, params)::Int64
menu = CreatePopupMenu(win32ui)
AppendMenu(self, menu, "&Locate module", "LocateModule")
AppendMenu(self, menu, win32con.MF_SEPARATOR)
AppendMenu(self, menu, "&Undo", "EditUndo")
AppendMenu(self, menu, "&Redo", "EditRedo")
AppendMenu(self, menu, win32con.MF_SEPARATOR)
AppendMenu(self, menu, "Cu&t", "EditCut")
AppendMenu(self, menu, "&Copy", "EditCopy")
AppendMenu(self, menu, "&Paste", "EditPaste")
AppendMenu(self, menu, win32con.MF_SEPARATOR)
AppendMenu(self, menu, "&Select all", "EditSelectAll")
AppendMenu(self, menu, "View &Whitespace", "ViewWhitespace", SCIGetViewWS(self))
AppendMenu(self, menu, "&Fixed Font", "ViewFixedFont", _GetColorizer(self).bUseFixed)
AppendMenu(self, menu, win32con.MF_SEPARATOR)
AppendMenu(self, menu, "&Goto line...", "GotoLine")
submenu = CreatePopupMenu(win32ui)
newitems = GetMenuItems(self.idle, "edit")
for (text, event) in newitems
AppendMenu(self, submenu, text, event)
end
flags = (win32con.MF_STRING | win32con.MF_ENABLED) | win32con.MF_POPUP
AppendMenu(menu, flags, GetHandle(submenu), "&Source code")
flags = (win32con.TPM_LEFTALIGN | win32con.TPM_LEFTBUTTON) | win32con.TPM_RIGHTBUTTON
TrackPopupMenu(menu, params[6], flags, self)
return 0
end

function OnCmdViewFold(self::SyntEditView, cid, code)
if cid == win32ui.ID_VIEW_FOLD_EXPAND_ALL
FoldExpandAllEvent(self, nothing)
elseif cid == win32ui.ID_VIEW_FOLD_EXPAND
FoldExpandEvent(self, nothing)
elseif cid == win32ui.ID_VIEW_FOLD_COLLAPSE_ALL
FoldCollapseAllEvent(self, nothing)
elseif cid == win32ui.ID_VIEW_FOLD_COLLAPSE
FoldCollapseEvent(self, nothing)
else
println("Unknown collapse/expand ID")
end
end

function OnUpdateViewFold(self::SyntEditView, cmdui)
if !(self.bFolding)
Enable(cmdui, 0)
return
end
id = cmdui.m_nID
if id ∈ [win32ui.ID_VIEW_FOLD_EXPAND_ALL, win32ui.ID_VIEW_FOLD_COLLAPSE_ALL]
Enable(cmdui)
else
enable = 0
lineno = LineFromChar(self, GetSel(self)[1])
foldable = SCIGetFoldLevel(self, lineno) & scintillacon.SC_FOLDLEVELHEADERFLAG
is_expanded = SCIGetFoldExpanded(self, lineno)
if id == win32ui.ID_VIEW_FOLD_EXPAND
if foldable && !(is_expanded)
enable = 1
end
elseif id == win32ui.ID_VIEW_FOLD_COLLAPSE
if foldable && is_expanded
enable = 1
end
end
Enable(cmdui, enable)
end
end

function OnCmdViewFoldTopLevel(self::SyntEditView, cid, code)
FoldTopLevelEvent(self, nothing)
end

function ToggleBookmarkEvent(self::SyntEditView, event, pos = -1)::Int64
#= Toggle a bookmark at the specified or current position =#
if pos == -1
pos, end_ = GetSel(self)
end
startLine = LineFromChar(self, pos)
MarkerToggle(GetDocument(self), startLine + 1, MARKER_BOOKMARK)
return 0
end

function GotoNextBookmarkEvent(self::SyntEditView, event, fromPos = -1)::Int64
#= Move to the next bookmark =#
if fromPos == -1
fromPos, end_ = GetSel(self)
end
startLine = LineFromChar(self, fromPos) + 1
nextLine = MarkerGetNext(GetDocument(self), startLine + 1, MARKER_BOOKMARK) - 1
if nextLine < 0
nextLine = MarkerGetNext(GetDocument(self), 0, MARKER_BOOKMARK) - 1
end
if nextLine < 0 || nextLine == (startLine - 1)
MessageBeep(win32api)
else
SCIEnsureVisible(self, nextLine)
SCIGotoLine(self, nextLine)
end
return 0
end

function TabKeyEvent(self::SyntEditView, event)::Int64
#= Insert an indent.  If no selection, a single indent, otherwise a block indent =#
if SCIAutoCActive(self)
SCIAutoCComplete(self)
return 0
end
return fire(self.bindings, "<<smart-indent>>", event)
end

function EnterKeyEvent(self::SyntEditView, event)
#= Handle the enter key with special handling for auto-complete =#
if SCIAutoCActive(self)
SCIAutoCComplete(self)
SCIAutoCCancel(self)
end
return fire(self.bindings, "<<newline-and-indent>>", event)
end

function ShowInteractiveWindowEvent(self::SyntEditView, event)
ShowInteractiveWindow(win32com_.gen_py.framework.interact)
end

function FoldTopLevelEvent(self::SyntEditView, event = nothing)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
try
Colorize(self)
maxLine = GetLineCount(self)
for lineSeek in 0:maxLine - 1
if SCIGetFoldLevel(self, lineSeek) & scintillacon.SC_FOLDLEVELHEADERFLAG
expanding = !SCIGetFoldExpanded(self, lineSeek)
has_break = true
break;
end
end
for lineSeek in lineSeek:maxLine - 1
level = SCIGetFoldLevel(self, lineSeek)
level_no = level & (scintillacon.SC_FOLDLEVELNUMBERMASK - scintillacon.SC_FOLDLEVELBASE)
is_header = level & scintillacon.SC_FOLDLEVELHEADERFLAG
if level_no == 0 && is_header
if expanding && !SCIGetFoldExpanded(self, lineSeek) || !(expanding) && SCIGetFoldExpanded(self, lineSeek)
SCIToggleFold(self, lineSeek)
end
end
end
finally
DoWaitCursor(win32ui, -1)
end
end

function FoldExpandSecondLevelEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
Colorize(self)
levels = [scintillacon.SC_FOLDLEVELBASE]
for lineno in 0:GetLineCount(self) - 1
level = SCIGetFoldLevel(self, lineno)
if !(level & scintillacon.SC_FOLDLEVELHEADERFLAG)
continue;
end
curr_level = level & scintillacon.SC_FOLDLEVELNUMBERMASK
if curr_level > levels[end]
append(levels, curr_level)
end
try
level_ind = index(levels, curr_level)
catch exn
if exn isa ValueError
break;
end
end
levels = levels[begin:level_ind + 1]
if level_ind == 1 && !SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
end
DoWaitCursor(win32ui, -1)
end

function FoldCollapseSecondLevelEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
Colorize(self)
levels = [scintillacon.SC_FOLDLEVELBASE]
for lineno in 0:GetLineCount(self) - 1
level = SCIGetFoldLevel(self, lineno)
if !(level & scintillacon.SC_FOLDLEVELHEADERFLAG)
continue;
end
curr_level = level & scintillacon.SC_FOLDLEVELNUMBERMASK
if curr_level > levels[end]
append(levels, curr_level)
end
try
level_ind = index(levels, curr_level)
catch exn
if exn isa ValueError
break;
end
end
levels = levels[begin:level_ind + 1]
if level_ind == 1 && SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
end
DoWaitCursor(win32ui, -1)
end

function FoldExpandEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
lineno = LineFromChar(self, GetSel(self)[1])
if SCIGetFoldLevel(self, lineno) & scintillacon.SC_FOLDLEVELHEADERFLAG && !SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
DoWaitCursor(win32ui, -1)
end

function FoldExpandAllEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
for lineno in 0:GetLineCount(self) - 1
if SCIGetFoldLevel(self, lineno) & scintillacon.SC_FOLDLEVELHEADERFLAG && !SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
end
DoWaitCursor(win32ui, -1)
end

function FoldCollapseEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
lineno = LineFromChar(self, GetSel(self)[1])
if SCIGetFoldLevel(self, lineno) & scintillacon.SC_FOLDLEVELHEADERFLAG && SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
DoWaitCursor(win32ui, -1)
end

function FoldCollapseAllEvent(self::SyntEditView, event)::Int64
if !(self.bFolding)
return 1
end
DoWaitCursor(win32ui, 1)
Colorize(self)
for lineno in 0:GetLineCount(self) - 1
if SCIGetFoldLevel(self, lineno) & scintillacon.SC_FOLDLEVELHEADERFLAG && SCIGetFoldExpanded(self, lineno)
SCIToggleFold(self, lineno)
end
end
DoWaitCursor(win32ui, -1)
end

using win32com_.gen_py.framework.editor.frame: EditorFrame
mutable struct SplitterFrame <: AbstractSplitterFrame
OnWindowSplit
end
function OnCreate(self::SplitterFrame, cs)::Int64
HookCommand(self, self.OnWindowSplit, win32ui.ID_WINDOW_SPLIT)
return 1
end

function OnWindowSplit(self::SplitterFrame, id, code)::Int64
DoKeyboardSplit(GetDlgItem(self, win32ui.AFX_IDW_PANE_FIRST))
return 1
end

using win32com_.gen_py.framework.editor.template: EditorTemplateBase
mutable struct SyntEditTemplate <: AbstractSyntEditTemplate
bSetMenus::Int64
makeDoc
makeFrame
makeView
res

            SyntEditTemplate(res = win32ui.IDR_TEXTTYPE, makeDoc = nothing, makeFrame = nothing, makeView = nothing) = begin
                if makeDoc === nothing
makeDoc = SyntEditDocument
end
if makeView === nothing
makeView = SyntEditView
end
if makeFrame === nothing
makeFrame = SplitterFrame
end
EditorTemplateBase.__init__(self, res, makeDoc, makeFrame, makeView)
                new(res , makeDoc , makeFrame , makeView )
            end
end
function CheckIDLEMenus(self::SyntEditTemplate, idle)
if self.bSetMenus != 0
return
end
self.bSetMenus = 1
submenu = CreatePopupMenu(win32ui)
newitems = GetMenuItems(idle, "edit")
flags = win32con.MF_STRING | win32con.MF_ENABLED
for (text, event) in newitems
id = get(bindings.event_to_commands, event)
if id != nothing
keyname = get_key_binding(win32com_.gen_py.scintilla.view.configManager, event, ["editor"])
if keyname != nothing
text = text * "\t" + keyname
end
AppendMenu(submenu, flags, id, text)
end
end
mainMenu = GetSharedMenu(self)
editMenu = GetSubMenu(mainMenu, 1)
AppendMenu(editMenu, win32con.MF_SEPARATOR, 0, "")
AppendMenu(editMenu, (win32con.MF_STRING | win32con.MF_POPUP) | win32con.MF_ENABLED, GetHandle(submenu), "&Source Code")
end

function _CreateDocTemplate(self::SyntEditTemplate, resourceId)
return CreateDocTemplate(win32ui, resourceId)
end

function CreateWin32uiDocument(self::SyntEditTemplate)
return DoCreateDoc(self)
end

function GetPythonPropertyPages(self::SyntEditTemplate)::Vector
#= Returns a list of property pages =#
return append!(GetPythonPropertyPages(EditorTemplateBase, self), [ScintillaFormatPropertyPage(configui)])
end

try
RemoveDocTemplate(GetApp(win32ui), editorTemplate)
catch exn
if exn isa NameError
#= pass =#
end
end
editorTemplate = SyntEditTemplate()
AddDocTemplate(GetApp(win32ui), editorTemplate)