# Framework Window classes.

# Most Pythonwin windows should use these classes rather than
# the raw MFC ones if they want Pythonwin specific functionality.
import win32com_.gen_py.mfc.window
import win32con


class MDIChildWnd(win32com_.gen_py.mfc.window.MDIChildWnd):
    def AutoRestore(self):
        "If the window is minimised or maximised, restore it."
        p = self.GetWindowPlacement()
        if p[1] == win32con.SW_MINIMIZE or p[1] == win32con.SW_SHOWMINIMIZED:
            self.SetWindowPlacement(p[0], win32con.SW_RESTORE, p[2], p[3], p[4])
