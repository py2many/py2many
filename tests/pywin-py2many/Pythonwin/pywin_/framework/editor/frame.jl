using PyCall
win32ui = pyimport("win32ui")
import win32com_.gen_py.framework.window

import win32con
import afxres
include("ModuleBrowser.jl")
abstract type AbstractEditorFrame <: Abstractwin32com_.gen_py.framework.window.MDIChildWnd end
mutable struct EditorFrame <: AbstractEditorFrame
sub_splitter
end
function OnCreateClient(self::EditorFrame, cp, context)
view = MakeView(context.template, context.doc)
browserView = BrowserView(ModuleBrowser, context.doc)
view2 = MakeView(context.template, context.doc)
splitter = CreateSplitter(win32ui)
style = win32con.WS_CHILD | win32con.WS_VISIBLE
CreateStatic(splitter, self, 1, 2, style, win32ui.AFX_IDW_PANE_FIRST)
sub_splitter = CreateSplitter(win32ui)
self.sub_splitter = CreateSplitter(win32ui)
CreateStatic(sub_splitter, splitter, 2, 1, style, win32ui.AFX_IDW_PANE_FIRST + 1)
CreateView(sub_splitter, view, 1, 0, (0, 0))
CreateView(splitter, browserView, 0, 0, (0, 0))
CreateView(sub_splitter, view2, 0, 0, (0, 0))
SetColumnInfo(splitter, 0, 10, 20)
SetActiveView(self, view)
end

function GetEditorView(self::EditorFrame)
if self.sub_splitter === nothing
return GetDlgItem(self, win32ui.AFX_IDW_PANE_FIRST)
end
v1 = GetPane(self.sub_splitter, 0, 0)
v2 = GetPane(self.sub_splitter, 1, 0)
r1 = GetWindowRect(v1)
r2 = GetWindowRect(v2)
if (r1[4] - r1[2]) > (r2[4] - r2[2])
return v1
end
return v2
end

function GetBrowserView(self::EditorFrame)
return GetAllViews(GetActiveDocument(self))[2]
end

function OnClose(self::EditorFrame)::Int64
doc = GetActiveDocument(self)
if !SaveModified(doc)
return 0
end
SetModifiedFlag(doc._obj_, false)
self.sub_splitter = nothing
DestroyBrowser(GetBrowserView(self))
return OnClose(self._obj_)
end
