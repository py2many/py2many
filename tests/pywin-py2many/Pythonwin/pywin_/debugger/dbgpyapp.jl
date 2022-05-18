using PyCall
win32ui = pyimport("win32ui")
using win32com_.gen_py.framework: interact
import win32con

import string

using win32com_.gen_py.framework: intpyapp
abstract type AbstractDebuggerPythonApp <: Abstractintpyapp.InteractivePythonApp end
version = "0.3.0"
mutable struct DebuggerPythonApp <: AbstractDebuggerPythonApp
    frame
end
function LoadMainFrame(self::DebuggerPythonApp)
    #= Create the main applications frame =#
    self.frame = CreateMainFrame(self)
    SetMainFrame(self, self.frame)
    LoadFrame(self.frame, win32ui.IDR_DEBUGGER, win32con.WS_OVERLAPPEDWINDOW)
    DragAcceptFiles(self.frame)
    ShowWindow(self.frame, win32con.SW_HIDE)
    UpdateWindow(self.frame)
    HookCommands(self)
end

function InitInstance(self::DebuggerPythonApp)
    SetAppName(win32ui, LoadString(win32ui, win32ui.IDR_DEBUGGER))
    SetRegistryKey(win32ui, "Python %s" % (sys.winver,))
    numMRU = GetProfileVal(win32ui, "Settings", "Recent File List Size", 10)
    LoadStdProfileSettings(win32ui, numMRU)
    LoadMainFrame(self)
    CreateInteractiveWindowUserPreference(interact)
    LoadSystemModules(self)
    LoadUserModules(self)
    EnableControlContainer(win32ui)
end
