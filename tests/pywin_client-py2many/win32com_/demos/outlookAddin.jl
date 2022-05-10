module outlookAddin
using PyCall
pythoncom = pyimport("pythoncom")
win32ui = pyimport("win32ui")

import winreg
import win32com.server.register
using win32com: universal
using win32com.server.exception: COMException
using win32com.client: gencache, DispatchWithEvents
import winerror

using win32com.client: constants

EnsureModule(gencache, "{00062FFF-0000-0000-C000-000000000046}", 0, 9, 0, true)
abstract type AbstractButtonEvent end
abstract type AbstractFolderEvent end
abstract type AbstractOutlookAddin end
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
    MessageBox(win32ui, "Hello from Python")
    return cancel
end

mutable struct FolderEvent <: AbstractFolderEvent

end
function OnItemAdd(self::FolderEvent, item)
    try
        println("An item was added to the inbox with subject:", Subject(item))
    catch exn
        if exn isa AttributeError
            println("An item was added to the inbox, but it has no subject! - ", repr(item))
        end
    end
end

mutable struct OutlookAddin <: AbstractOutlookAddin
    inboxItems::Any
    _com_interfaces_::Vector{String}
    _public_methods_::Vector
    _reg_clsctx_::Any
    _reg_clsid_::String
    _reg_policy_spec_::String
    _reg_progid_::String

    OutlookAddin(
        inboxItems::Any,
        _com_interfaces_::Vector{String} = ["_IDTExtensibility2"],
        _public_methods_::Vector = [],
        _reg_clsctx_::Any = CLSCTX_INPROC_SERVER(pythoncom),
        _reg_clsid_::String = "{0F47D9F3-598B-4d24-B7E3-92AC15ED27E2}",
        _reg_policy_spec_::String = "win32com.server.policy.EventHandlerPolicy",
        _reg_progid_::String = "Python.Test.OutlookAddin",
    ) = new(
        inboxItems,
        _com_interfaces_,
        _public_methods_,
        _reg_clsctx_,
        _reg_clsid_,
        _reg_policy_spec_,
        _reg_progid_,
    )
end
function OnConnection(self::OutlookAddin, application, connectMode, addin, custom)
    println("OnConnection", application, connectMode, addin, custom)
    activeExplorer = ActiveExplorer(application)
    if activeExplorer != nothing
        bars = CommandBars(activeExplorer)
        toolbar = Item(bars, "Standard")
        item = Add(toolbar.Controls, constants.msoControlButton, true)
        item = DispatchWithEvents(item, ButtonEvent)
        self.toolbarButton = DispatchWithEvents(item, ButtonEvent)
        Caption(item) = "Python"
        TooltipText(item) = "Click for Python"
        Enabled(item) = true
    end
    inbox = GetDefaultFolder(application.Session, constants.olFolderInbox)
    self.inboxItems = DispatchWithEvents(Items(inbox), FolderEvent)
end

function OnDisconnection(self::OutlookAddin, mode, custom)
    println("OnDisconnection")
end

function OnAddInsUpdate(self::OutlookAddin, custom)
    println("OnAddInsUpdate", custom)
end

function OnStartupComplete(self::OutlookAddin, custom)
    println("OnStartupComplete", custom)
end

function OnBeginShutdown(self::OutlookAddin, custom)
    println("OnBeginShutdown", custom)
end

function RegisterAddin(klass)
    key = CreateKey(
        winreg,
        HKEY_CURRENT_USER(winreg),
        "Software\\Microsoft\\Office\\Outlook\\Addins",
    )
    subkey = CreateKey(winreg, key, _reg_progid_(klass))
    SetValueEx(winreg, subkey, "CommandLineSafe", 0, REG_DWORD(winreg), 0)
    SetValueEx(winreg, subkey, "LoadBehavior", 0, REG_DWORD(winreg), 3)
    SetValueEx(winreg, subkey, "Description", 0, REG_SZ(winreg), _reg_progid_(klass))
    SetValueEx(winreg, subkey, "FriendlyName", 0, REG_SZ(winreg), _reg_progid_(klass))
end

function UnregisterAddin(klass)
    try
        DeleteKey(
            winreg,
            HKEY_CURRENT_USER(winreg),
            "Software\\Microsoft\\Office\\Outlook\\Addins\\" + _reg_progid_(klass),
        )
    catch exn
        if exn isa WindowsError
            #= pass =#
        end
    end
end

function main()
    UseCommandLine(win32com.server.register, OutlookAddin)
    if "--unregister" in append!([PROGRAM_FILE], ARGS)
        UnregisterAddin(OutlookAddin)
    else
        RegisterAddin(OutlookAddin)
    end
end

main()
end
