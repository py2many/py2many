using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
include("app.jl")

import win32con

using win32com_.gen_py.mfc: dialog
abstract type AbstractAppDialog <: Abstractdialog.Dialog end
abstract type AbstractDialogApp <: Abstractapp.CApp end
error = "Dialog Application Error"
mutable struct AppDialog <: AbstractAppDialog
    #= The dialog box for the application =#
    iconId
    dll

    AppDialog(id, dll = nothing) = begin
        dialog.Dialog.__init__(self, id, dll)
        new(id, dll)
    end
end
function OnInitDialog(self::AppDialog)
    return OnInitDialog(dialog.Dialog)
end

function OnPaint(self::AppDialog)
    if !IsIconic(self)
        return OnPaint(self._obj_)
    end
    DefWindowProc(self, win32con.WM_ICONERASEBKGND, GetHandleOutput(dc), 0)
    left, top, right, bottom = GetClientRect(self)
    left = (right - GetSystemMetrics(win32api, win32con.SM_CXICON)) >> 1
    top = (bottom - GetSystemMetrics(win32api, win32con.SM_CYICON)) >> 1
    hIcon = LoadIcon(GetApp(win32ui), self.iconId)
    DrawIcon(GetDC(self), (left, top), hIcon)
end

function OnEraseBkgnd(self::AppDialog, dc)::Int64
    if IsIconic(self)
        return 1
    else
        return OnEraseBkgnd(self._obj_, dc)
    end
end

function OnQueryDragIcon(self::AppDialog)
    return LoadIcon(GetApp(win32ui), self.iconId)
end

function PreDoModal(self::AppDialog)
    #= pass =#
end

mutable struct DialogApp <: AbstractDialogApp
    #= An application class, for an app with main dialog box =#
    dlg
    frame
end
function InitInstance(self::DialogApp)
    LoadStdProfileSettings(win32ui)
    EnableControlContainer(win32ui)
    Enable3dControls(win32ui)
    self.dlg = CreateDialog(self)
    self.frame = CreateDialog(self)
    if self.frame === nothing
        throw(error("No dialog was created by CreateDialog()"))
        return
    end
    InitDlgInstance(self._obj_, self.dlg)
    PreDoModal(self)
    PreDoModal(self.dlg)
    DoModal(self.dlg)
end

function CreateDialog(self::DialogApp)
    #= pass =#
end

function PreDoModal(self::DialogApp)
    #= pass =#
end
