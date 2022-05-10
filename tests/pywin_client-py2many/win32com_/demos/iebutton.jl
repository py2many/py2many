module iebutton
#= 
This sample implements a simple IE Button COM server
with access to the IWebBrowser2 interface.

To demonstrate:
* Execute this script to register the server.
* Open Pythonwin's Tools -> Trace Collector Debugging Tool, so you can
  see the output of 'print' statements in this demo.
* Open a new IE instance.  The toolbar should have a new "scissors" icon,
  with tooltip text "IE Button" - this is our new button - click it.
* Switch back to the Pythonwin window - you should see:
   IOleCommandTarget::Exec called.
  This is the button being clicked.  Extending this to do something more
  useful is left as an exercise.

Contribtions to this sample to make it a little "friendlier" welcome!
 =#
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import winreg

using win32com: universal
using win32com.client: gencache, DispatchWithEvents, Dispatch
using win32com.client: constants, getevents
import win32com.server.register
import win32com


try
    GetConsoleTitle(win32api)
catch exn
    if exn isa error(win32api)
        import win32traceutil
    end
end
using win32com.axcontrol: axcontrol

EnsureModule(win32com.client.gencache, "{EAB22AC0-30C1-11CF-A7EB-0000C05BAE0B}", 0, 1, 1)
abstract type AbstractStub end
abstract type AbstractIEButton end
abstract type AbstractPyWin32InternetExplorerButton <: AbstractIEButton end
IObjectWithSite_methods = ["SetSite", "GetSite"]
IOleCommandTarget_methods = ["Exec", "QueryStatus"]
_iebutton_methods_ = append!(IOleCommandTarget_methods, IObjectWithSite_methods)
_iebutton_com_interfaces_ = [axcontrol.IID_IOleCommandTarget, axcontrol.IID_IObjectWithSite]
mutable struct Stub <: AbstractStub
    #= 
        this class serves as a method stub,
        outputting debug info whenever the object
        is being called.
         =#
    name::Any
end
function __call__(self::Stub)
    println("STUB: ", self.name, args)
end

mutable struct IEButton <: AbstractIEButton
    #= 
        The actual COM server class
         =#
    _reg_clsid_::Any
    webbrowser::Any
    _button_text_::String
    _com_interfaces_::Vector
    _hot_icon_::String
    _icon_::String
    _public_methods_::Vector{String}
    _reg_clsctx_::Any
    _tool_tip_::String

    IEButton(
        _button_text_::String = "IE Button",
        _com_interfaces_::Vector = _iebutton_com_interfaces_,
        _hot_icon_::String = "",
        _icon_::String = "",
        _public_methods_::Vector{String} = _iebutton_methods_,
        _reg_clsctx_ = CLSCTX_INPROC_SERVER(pythoncom),
        _tool_tip_::String = "An example implementation for an IE Button.",
    ) = begin
        for method in self._public_methods_
            if !hasattr(self, method)
                @printf("providing default stub for %s", method)
                setattr(self, method, Stub(method))
            end
        end
        new(
            _button_text_,
            _com_interfaces_,
            _hot_icon_,
            _icon_,
            _public_methods_,
            _reg_clsctx_,
            _tool_tip_,
        )
    end
end
function QueryStatus(self::IEButton, pguidCmdGroup, prgCmds, cmdtextf)::Tuple
    result = []
    for (id, flags) in prgCmds
        flags |= axcontrol.OLECMDF_SUPPORTED | axcontrol.OLECMDF_ENABLED
        push!(result, (id, flags))
    end
    if cmdtextf === nothing
        cmdtext = nothing
    elseif cmdtextf == axcontrol.OLECMDTEXTF_NAME
        cmdtext = "IEButton Name"
    else
        cmdtext = "IEButton State"
    end
    return (result, cmdtext)
end

function Exec(self::IEButton, pguidCmdGroup, nCmdID, nCmdExecOpt, pvaIn)
    println(pguidCmdGroup, nCmdID, nCmdExecOpt, pvaIn)
    println("IOleCommandTarget::Exec called.")
end

function SetSite(self::IEButton, unknown)
    if unknown
        cmdtarget = QueryInterface(unknown, axcontrol.IID_IOleCommandTarget)
        serviceprovider = QueryInterface(cmdtarget, IID_IServiceProvider(pythoncom))
        self.webbrowser = Dispatch(
            win32com.client,
            QueryService(
                serviceprovider,
                "{0002DF05-0000-0000-C000-000000000046}",
                IID_IDispatch(pythoncom),
            ),
        )
    else
        self.webbrowser = nothing
    end
end

function GetClassID(self::IEButton)::IEButton
    return self._reg_clsid_
end

function register(classobj)
    subKeyCLSID =
        "SOFTWARE\\Microsoft\\Internet Explorer\\Extensions\\%38s" % _reg_clsid_(classobj)
    try
        hKey = CreateKey(winreg, HKEY_LOCAL_MACHINE(winreg), subKeyCLSID)
        subKey = SetValueEx(
            winreg,
            hKey,
            "ButtonText",
            0,
            REG_SZ(winreg),
            _button_text_(classobj),
        )
        SetValueEx(winreg, hKey, "ClsidExtension", 0, REG_SZ(winreg), _reg_clsid_(classobj))
        SetValueEx(
            winreg,
            hKey,
            "CLSID",
            0,
            REG_SZ(winreg),
            "{1FBA04EE-3024-11D2-8F1F-0000F87ABD16}",
        )
        SetValueEx(winreg, hKey, "Default Visible", 0, REG_SZ(winreg), "Yes")
        SetValueEx(winreg, hKey, "ToolTip", 0, REG_SZ(winreg), _tool_tip_(classobj))
        SetValueEx(winreg, hKey, "Icon", 0, REG_SZ(winreg), _icon_(classobj))
        SetValueEx(winreg, hKey, "HotIcon", 0, REG_SZ(winreg), _hot_icon_(classobj))
    catch exn
        if exn isa WindowsError
            println("Couldn\'t set standard toolbar reg keys.")
        end
    end
end

function unregister(classobj)
    subKeyCLSID =
        "SOFTWARE\\Microsoft\\Internet Explorer\\Extensions\\%38s" % _reg_clsid_(classobj)
    try
        hKey = CreateKey(winreg, HKEY_LOCAL_MACHINE(winreg), subKeyCLSID)
        subKey = DeleteValue(winreg, hKey, "ButtonText")
        DeleteValue(winreg, hKey, "ClsidExtension")
        DeleteValue(winreg, hKey, "CLSID")
        DeleteValue(winreg, hKey, "Default Visible")
        DeleteValue(winreg, hKey, "ToolTip")
        DeleteValue(winreg, hKey, "Icon")
        DeleteValue(winreg, hKey, "HotIcon")
        DeleteKey(winreg, HKEY_LOCAL_MACHINE(winreg), subKeyCLSID)
    catch exn
        if exn isa WindowsError
            println("Couldn\'t delete Standard toolbar regkey.")
        end
    end
end

mutable struct PyWin32InternetExplorerButton <: AbstractPyWin32InternetExplorerButton
    _button_text_::String
    _hot_icon_::String
    _icon_::String
    _reg_clsid_::String
    _reg_desc_::String
    _reg_progid_::String
    _tool_tip_::String

    PyWin32InternetExplorerButton(
        _button_text_::String = "IE Button",
        _hot_icon_::String = _icon_,
        _icon_::String = "",
        _reg_clsid_::String = "{104B66A9-9E68-49D1-A3F5-94754BE9E0E6}",
        _reg_desc_::String = "Test Button",
        _reg_progid_::String = "PyWin32.IEButton",
        _tool_tip_::String = "An example implementation for an IE Button.",
    ) = new(
        _button_text_,
        _hot_icon_,
        _icon_,
        _reg_clsid_,
        _reg_desc_,
        _reg_progid_,
        _tool_tip_,
    )
end

function DllRegisterServer()
    register(PyWin32InternetExplorerButton)
end

function DllUnregisterServer()
    unregister(PyWin32InternetExplorerButton)
end

function main()
    UseCommandLine(
        win32com.server.register,
        PyWin32InternetExplorerButton,
        DllRegisterServer,
        DllUnregisterServer,
    )
end

main()
end
