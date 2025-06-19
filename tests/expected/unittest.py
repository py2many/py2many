import unittest

class UnitTestTranslation(unittest.TestCase):
    def testSequences(self):
        x = [1, 2]
        z = x  # Added

        self.assertEqual(z, [1, 2])

        x = [1, 2, 3]
        y = x
        self.assertTrue(x is y)

if __name__ =="__main__":
    unittest.main()