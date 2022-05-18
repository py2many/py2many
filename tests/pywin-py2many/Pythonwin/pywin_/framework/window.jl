import win32com_.gen_py.mfc.window
import win32con
abstract type AbstractMDIChildWnd <: Abstractwin32com_.gen_py.mfc.window.MDIChildWnd end
mutable struct MDIChildWnd <: AbstractMDIChildWnd

end
function AutoRestore(self::MDIChildWnd)
#= If the window is minimised or maximised, restore it. =#
p = GetWindowPlacement(self)
if p[2] == win32con.SW_MINIMIZE || p[2] == win32con.SW_SHOWMINIMIZED
SetWindowPlacement(self, p[1], win32con.SW_RESTORE, p[3], p[4], p[5])
end
end
