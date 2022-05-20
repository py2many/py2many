#= login -- PythonWin user ID and password dialog box

(Adapted from originally distributed with Mark Hammond's PythonWin - 
this now replaces it!)

login.GetLogin() displays a modal "OK/Cancel" dialog box with input
fields for a user ID and password. The password field input is masked
with *'s. GetLogin takes two optional parameters, a window title, and a
default user ID. If these parameters are omitted, the title defaults to
"Login", and the user ID is left blank. GetLogin returns a (userid, password)
tuple. GetLogin can be called from scripts running on the console - i.e. you
don't need to write a full-blown GUI app to use it.

login.GetPassword() is similar, except there is no username field.

Example:
import win32com_.gen_py.dialogs.login
title = "FTP Login"
def_user = "fred"
userid, password = win32com_.gen_py.dialogs.login.GetLogin(title, def_user)

Jim Eggleston, 28 August 1996
Merged with dlgpass and moved to win32com_.gen_py.dialogs by Mark Hammond Jan 1998.
 =#
using Printf
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")

import win32con
using win32com_.gen_py.mfc: dialog
abstract type AbstractLoginDlg <: Abstractdialog.Dialog end
abstract type AbstractPasswordDlg <: Abstractdialog.Dialog end
function MakeLoginDlgTemplate(title)
    style =
        (
            (
                ((win32con.DS_MODALFRAME | win32con.WS_POPUP) | win32con.WS_VISIBLE) |
                win32con.WS_CAPTION
            ) | win32con.WS_SYSMENU
        ) | win32con.DS_SETFONT
    cs = win32con.WS_CHILD | win32con.WS_VISIBLE
    dlg = [[title, (0, 0, 184, 40), style, nothing, (8, "MS Sans Serif")]]
    push!(dlg, [130, "User ID:", -1, (7, 9, 69, 9), cs | win32con.SS_LEFT])
    s = (cs | win32con.WS_TABSTOP) | win32con.WS_BORDER
    push!(dlg, ["EDIT", nothing, win32ui.IDC_EDIT1, (50, 7, 60, 12), s])
    push!(dlg, [130, "Password:", -1, (7, 22, 69, 9), cs | win32con.SS_LEFT])
    s = (cs | win32con.WS_TABSTOP) | win32con.WS_BORDER
    push!(
        dlg,
        ["EDIT", nothing, win32ui.IDC_EDIT2, (50, 20, 60, 12), s | win32con.ES_PASSWORD],
    )
    s = cs | win32con.WS_TABSTOP
    push!(dlg, [128, "OK", win32con.IDOK, (124, 5, 50, 14), s | win32con.BS_DEFPUSHBUTTON])
    s = win32con.BS_PUSHBUTTON | s
    push!(dlg, [128, "Cancel", win32con.IDCANCEL, (124, 20, 50, 14), s])
    return dlg
end

function MakePasswordDlgTemplate(title)
    style =
        (
            (
                ((win32con.DS_MODALFRAME | win32con.WS_POPUP) | win32con.WS_VISIBLE) |
                win32con.WS_CAPTION
            ) | win32con.WS_SYSMENU
        ) | win32con.DS_SETFONT
    cs = win32con.WS_CHILD | win32con.WS_VISIBLE
    dlg = [[title, (0, 0, 177, 45), style, nothing, (8, "MS Sans Serif")]]
    push!(dlg, [130, "Password:", -1, (7, 7, 69, 9), cs | win32con.SS_LEFT])
    s = (cs | win32con.WS_TABSTOP) | win32con.WS_BORDER
    push!(
        dlg,
        ["EDIT", nothing, win32ui.IDC_EDIT1, (50, 7, 60, 12), s | win32con.ES_PASSWORD],
    )
    s = (cs | win32con.WS_TABSTOP) | win32con.BS_PUSHBUTTON
    push!(dlg, [128, "OK", win32con.IDOK, (124, 5, 50, 14), s | win32con.BS_DEFPUSHBUTTON])
    push!(dlg, [128, "Cancel", win32con.IDCANCEL, (124, 22, 50, 14), s])
    return dlg
end

mutable struct LoginDlg <: AbstractLoginDlg
    Cancel::Int64

    LoginDlg(title, Cancel::Int64 = 0) = begin
        dialog.Dialog.__init__(self, MakeLoginDlgTemplate(title))
        AddDDX(win32ui.IDC_EDIT1, "userid")
        AddDDX(win32ui.IDC_EDIT2, "password")
        new(title, Cancel)
    end
end

function GetLogin(title = "Login", userid = "", password = "")::Tuple
    d = LoginDlg(title)
    d["userid"] = userid
    d["password"] = password
    if DoModal(d) != win32con.IDOK
        return (nothing, nothing)
    else
        return (d["userid"], d["password"])
    end
end

mutable struct PasswordDlg <: AbstractPasswordDlg
    PasswordDlg(title) = begin
        dialog.Dialog.__init__(self, MakePasswordDlgTemplate(title))
        AddDDX(win32ui.IDC_EDIT1, "password")
        new(title)
    end
end

function GetPassword(title = "Password", password = "")::PasswordDlg
    d = PasswordDlg(title)
    d["password"] = password
    if DoModal(d) != win32con.IDOK
        return nothing
    end
    return d["password"]
end

if abspath(PROGRAM_FILE) == @__FILE__
    title = "Login"
    def_user = ""
    if length(append!([PROGRAM_FILE], ARGS)) > 1
        title = append!([PROGRAM_FILE], ARGS)[2]
    end
    if length(append!([PROGRAM_FILE], ARGS)) > 2
        def_userid = append!([PROGRAM_FILE], ARGS)[3]
    end
    userid, password = GetLogin(title, def_user)
    if userid == password === nothing
        println("User pressed Cancel")
    else
        println("User ID: $(userid)")
        println("Password:$(password)")
        newpassword = GetPassword("Reenter just for fun", password)
        if newpassword === nothing
            println("User cancelled")
        else
            what = ""
            if newpassword != password
                what = "not "
            end
            @printf("The passwords did %smatch\n", what)
        end
    end
end
