# Test AXScripting the best we can in an automated fashion...
import win32api, os, sys

import win32com_.axscript
import win32com_.axscript.client

import unittest
import win32com_.test.util

verbose = "-v" in sys.argv


class AXScript(win32com_.test.util.TestCase):
    def setUp(self):
        file = win32api.GetFullPathName(
            os.path.join(win32com_.axscript.client.__path__[0], "pyscript.py")
        )
        from win32com_.test.util import RegisterPythonServer

        self.verbose = verbose
        RegisterPythonServer(file, "python", verbose=self.verbose)

    def testHost(self):
        file = win32api.GetFullPathName(
            os.path.join(win32com_.axscript.__path__[0], "test\\testHost.py")
        )
        cmd = '%s "%s"' % (win32api.GetModuleFileName(0), file)
        if verbose:
            print("Testing Python Scripting host")
        win32com_.test.util.ExecuteShellCommand(cmd, self)

    def testCScript(self):
        file = win32api.GetFullPathName(
            os.path.join(win32com_.axscript.__path__[0], "Demos\\Client\\wsh\\test.pys")
        )
        cmd = 'cscript.exe "%s"' % (file)
        if verbose:
            print("Testing Windows Scripting host with Python script")
        win32com_.test.util.ExecuteShellCommand(cmd, self)


if __name__ == "__main__":
    win32com_.test.util.testmain()
