using PyCall
win32ui = pyimport("win32ui")
include("object.jl")

import win32con
abstract type AbstractWnd <: Abstractobject.CmdTarget end
abstract type AbstractFrameWnd <: AbstractWnd end
abstract type AbstractMDIChildWnd <: AbstractFrameWnd end
abstract type AbstractMDIFrameWnd <: AbstractFrameWnd end
mutable struct Wnd <: AbstractWnd
initobj

            Wnd(initobj = nothing) = begin
                object.CmdTarget.__init__(self, initobj)
if _obj_
_obj_.HookMessage(OnDestroy, win32con.WM_DESTROY)
end
                new(initobj )
            end
end
function OnDestroy(self::Wnd, msg)
#= pass =#
end

mutable struct FrameWnd <: AbstractFrameWnd


            FrameWnd(wnd) = begin
                Wnd(wnd)
                new(wnd)
            end
end

mutable struct MDIChildWnd <: AbstractMDIChildWnd
wnd

            MDIChildWnd(wnd = nothing) = begin
                if wnd === nothing
wnd = win32ui.CreateMDIChild()
end
FrameWnd(wnd)
                new(wnd )
            end
end
function OnCreateClient(self::MDIChildWnd, cp, context)
if context != nothing && context.template != nothing
CreateView(context.template, self, context)
end
end

mutable struct MDIFrameWnd <: AbstractMDIFrameWnd
wnd

            MDIFrameWnd(wnd = nothing) = begin
                if wnd === nothing
wnd = win32ui.CreateMDIFrame()
end
FrameWnd(wnd)
                new(wnd )
            end
end
