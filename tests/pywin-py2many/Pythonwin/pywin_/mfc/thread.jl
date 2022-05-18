using PyCall
win32ui = pyimport("win32ui")
include("object.jl")

abstract type AbstractWinThread <: Abstractobject.CmdTarget end
abstract type AbstractWinApp <: AbstractWinThread end
mutable struct WinThread <: AbstractWinThread
initObj

            WinThread(initObj = nothing) = begin
                if initObj === nothing
initObj = win32ui.CreateThread()
end
object.CmdTarget.__init__(self, initObj)
                new(initObj )
            end
end
function InitInstance(self::WinThread)
#= pass =#
end

function ExitInstance(self::WinThread)
#= pass =#
end

mutable struct WinApp <: AbstractWinApp
initApp

            WinApp(initApp = nothing) = begin
                if initApp === nothing
initApp = win32ui.GetApp()
end
WinThread(initApp)
                new(initApp )
            end
end
