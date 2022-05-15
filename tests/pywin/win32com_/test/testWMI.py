from win32com_.client import GetObject
import win32com_.test.util

import unittest


class Simple(win32com_.test.util.TestCase):
    def testit(self):
        cses = GetObject("WinMgMts:").InstancesOf("Win32_Process")
        vals = []
        for cs in cses:
            val = cs.Properties_("Caption").Value
            vals.append(val)
        self.assertFalse(len(vals) < 5, "We only found %d processes!" % len(vals))


if __name__ == "__main__":
    unittest.main()
