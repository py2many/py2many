module excelAddin
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32ui = pyimport("win32ui")

import win32con
import winreg
import win32com.server.register
using win32com: universal
using win32com.server.exception: COMException
using win32com.client: gencache, DispatchWithEvents
import winerror

using win32com.client: constants, Dispatch

EnsureModule(gencache, "{00020813-0000-0000-C000-000000000046}", 0, 1, 3, true)
abstract type AbstractButtonEvent end
abstract type AbstractExcelAddin end
EnsureModule(gencache, "{2DF8D04C-5BFA-101B-BDE5-00AA0044DE52}", 0, 2, 1, true)
RegisterInterfaces(
    universal,
    "{AC0714F2-3D04-11D1-AE7D-00A0C90F26F4}",
    0,
    1,
    0,
    ["_IDTExtensibility2"],
)
mutable struct ButtonEvent <: AbstractButtonEvent

end
function OnClick(self::ButtonEvent, button, cancel)
    MessageBox(win32ui, "Hello from Python", "Python Test", win32con.MB_OKCANCEL)
    return cancel
end

mutable struct ExcelAddin <: AbstractExcelAddin
    _com_interfaces_::Vector{String}
    _public_methods_::Vector
    _reg_clsctx_::Any
    _reg_clsid_::String
    _reg_policy_spec_::String
    _reg_progid_::String
    appHostApp::Any

    ExcelAddin(
        _com_interfaces_::Vector{String} = ["_IDTExtensibility2"],
        _public_methods_::Vector = [],
        _reg_clsctx_::Any = CLSCTX_INPROC_SERVER(pythoncom),
        _reg_clsid_::String = "{C5482ECA-F559-45A0-B078-B2036E6F011A}",
        _reg_policy_spec_::String = "win32com.server.policy.EventHandlerPolicy",
        _reg_progid_::String = "Python.Test.ExcelAddin",
        appHostApp::Any = nothing,
    ) = new(
        _com_interfaces_,
        _public_methods_,
        _reg_clsctx_,
        _reg_clsid_,
        _reg_policy_spec_,
        _reg_progid_,
        appHostApp,
    )
end
function OnConnection(self::ExcelAddin, application, connectMode, addin, custom)
    println("OnConnection", application, connectMode, addin, custom)
    try
        self.appHostApp = application
        cbcMyBar = Add(
            self.appHostApp.CommandBars,
            "PythonBar",
            constants.msoBarTop,
            constants.msoBarTypeNormal,
            true,
        )
        btnMyButton = Add(cbcMyBar.Controls, constants.msoControlButton, "Greetings")
        btnMyButton = DispatchWithEvents(btnMyButton, ButtonEvent)
        self.toolbarButton = DispatchWithEvents(btnMyButton, ButtonEvent)
        Style(btnMyButton) = constants.msoButtonCaption
        BeginGroup(btnMyButton) = true
        Caption(btnMyButton) = "&Python"
        TooltipText(btnMyButton) = "Python rules the World"
        Width(btnMyButton) = "34"
        Visible(cbcMyBar) = true
    catch exn
        let xxx_todo_changeme = exn
            if xxx_todo_changeme isa com_error(pythoncom)
                hr, msg, exc, arg = args(xxx_todo_changeme)
                @printf("The Excel call failed with code %d: %s", (hr, msg))
                if exc === nothing
                    println("There is no extended error information")
                else
                    wcode, source, text, helpFile, helpId, scode = exc
                    println("The source of the error is", source)
                    println("The error message is", text)
                    @printf("More info can be found in %s (id=%d)", (helpFile, helpId))
                end
            end
        end
    end
end

function OnDisconnection(self::ExcelAddin, mode, custom)
    println("OnDisconnection")
    self.appHostApp.CommandBars("PythonBar").Delete
    self.appHostApp = nothing
end

function OnAddInsUpdate(self::ExcelAddin, custom)
    println("OnAddInsUpdate", custom)
end

function OnStartupComplete(self::ExcelAddin, custom)
    println("OnStartupComplete", custom)
end

function OnBeginShutdown(self::ExcelAddin, custom)
    println("OnBeginShutdown", custom)
end

function RegisterAddin(klass)
    key = CreateKey(
        winreg,
        HKEY_CURRENT_USER(winreg),
        "Software\\Microsoft\\Office\\Excel\\Addins",
    )
    subkey = CreateKey(winreg, key, _reg_progid_(klass))
    SetValueEx(winreg, subkey, "CommandLineSafe", 0, REG_DWORD(winreg), 0)
    SetValueEx(winreg, subkey, "LoadBehavior", 0, REG_DWORD(winreg), 3)
    SetValueEx(winreg, subkey, "Description", 0, REG_SZ(winreg), "Excel Addin")
    SetValueEx(winreg, subkey, "FriendlyName", 0, REG_SZ(winreg), "A Simple Excel Addin")
end

function UnregisterAddin(klass)
    try
        DeleteKey(
            winreg,
            HKEY_CURRENT_USER(winreg),
            "Software\\Microsoft\\Office\\Excel\\Addins\\" + _reg_progid_(klass),
        )
    catch exn
        if exn isa WindowsError
            #= pass =#
        end
    end
end

function main()
    UseCommandLine(win32com.server.register, ExcelAddin)
    if "--unregister" in append!([PROGRAM_FILE], ARGS)
        UnregisterAddin(ExcelAddin)
    else
        RegisterAddin(ExcelAddin)
    end
end

main()
end
