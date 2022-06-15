"""Test correct treatment of hex/oct constants.

This is complex because of changes due to PEP 237.
"""

import unittest


class TestHexOctBin(unittest.TestCase):
    def test_hex_baseline(self):
        # A few upper/lowercase tests
        self.assertEqual(0x0, 0x0)
        self.assertEqual(0x1, 0x1)
        self.assertEqual(0x123456789ABCDEF, 0x123456789ABCDEF)
        # Baseline tests
        self.assertEqual(0x0, 0)
        self.assertEqual(0x10, 16)
        self.assertEqual(0x7FFFFFFF, 2147483647)
        self.assertEqual(0x7FFFFFFFFFFFFFFF, 9223372036854775807)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0x0), 0)
        self.assertEqual(-(0x10), -16)
        self.assertEqual(-(0x7FFFFFFF), -2147483647)
        self.assertEqual(-(0x7FFFFFFFFFFFFFFF), -9223372036854775807)
        # Ditto with a minus sign and NO parentheses
        self.assertEqual(-0x0, 0)
        self.assertEqual(-0x10, -16)
        self.assertEqual(-0x7FFFFFFF, -2147483647)
        self.assertEqual(-0x7FFFFFFFFFFFFFFF, -9223372036854775807)

    def test_hex_unsigned(self):
        # Positive constants
        self.assertEqual(0x80000000, 2147483648)
        self.assertEqual(0xFFFFFFFF, 4294967295)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0x80000000), -2147483648)
        self.assertEqual(-(0xFFFFFFFF), -4294967295)
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(-0x80000000, -2147483648)
        self.assertEqual(-0xFFFFFFFF, -4294967295)

        # Positive constants
        self.assertEqual(0x8000000000000000, 9223372036854775808)
        self.assertEqual(0xFFFFFFFFFFFFFFFF, 18446744073709551615)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0x8000000000000000), -9223372036854775808)
        self.assertEqual(-(0xFFFFFFFFFFFFFFFF), -18446744073709551615)
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(-0x8000000000000000, -9223372036854775808)
        self.assertEqual(-0xFFFFFFFFFFFFFFFF, -18446744073709551615)

    def test_oct_baseline(self):
        # A few upper/lowercase tests
        self.assertEqual(0o0, 0o0)
        self.assertEqual(0o1, 0o1)
        self.assertEqual(0o1234567, 0o1234567)
        # Baseline tests
        self.assertEqual(0o0, 0)
        self.assertEqual(0o20, 16)
        self.assertEqual(0o17777777777, 2147483647)
        self.assertEqual(0o777777777777777777777, 9223372036854775807)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0o0), 0)
        self.assertEqual(-(0o20), -16)
        self.assertEqual(-(0o17777777777), -2147483647)
        self.assertEqual(-(0o777777777777777777777), -9223372036854775807)
        # Ditto with a minus sign and NO parentheses
        self.assertEqual(-0o0, 0)
        self.assertEqual(-0o20, -16)
        self.assertEqual(-0o17777777777, -2147483647)
        self.assertEqual(-0o777777777777777777777, -9223372036854775807)

    def test_oct_unsigned(self):
        # Positive constants
        self.assertEqual(0o20000000000, 2147483648)
        self.assertEqual(0o37777777777, 4294967295)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0o20000000000), -2147483648)
        self.assertEqual(-(0o37777777777), -4294967295)
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(-0o20000000000, -2147483648)
        self.assertEqual(-0o37777777777, -4294967295)

        # Positive constants
        self.assertEqual(0o1000000000000000000000, 9223372036854775808)
        self.assertEqual(0o1777777777777777777777, 18446744073709551615)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0o1000000000000000000000), -9223372036854775808)
        self.assertEqual(-(0o1777777777777777777777), -18446744073709551615)
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(-0o1000000000000000000000, -9223372036854775808)
        self.assertEqual(-0o1777777777777777777777, -18446744073709551615)

    def test_bin_baseline(self):
        # A few upper/lowercase tests
        self.assertEqual(0b0, 0b0)
        self.assertEqual(0b1, 0b1)
        self.assertEqual(0b10101010101, 0b10101010101)
        # Baseline tests
        self.assertEqual(0b0, 0)
        self.assertEqual(0b10000, 16)
        self.assertEqual(0b1111111111111111111111111111111, 2147483647)
        self.assertEqual(
            0b111111111111111111111111111111111111111111111111111111111111111,
            9223372036854775807,
        )
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0b0), 0)
        self.assertEqual(-(0b10000), -16)
        self.assertEqual(-(0b1111111111111111111111111111111), -2147483647)
        self.assertEqual(
            -(0b111111111111111111111111111111111111111111111111111111111111111),
            -9223372036854775807,
        )
        # Ditto with a minus sign and NO parentheses
        self.assertEqual(-0b0, 0)
        self.assertEqual(-0b10000, -16)
        self.assertEqual(-0b1111111111111111111111111111111, -2147483647)
        self.assertEqual(
            -0b111111111111111111111111111111111111111111111111111111111111111,
            -9223372036854775807,
        )

    def test_bin_unsigned(self):
        # Positive constants
        self.assertEqual(0b10000000000000000000000000000000, 2147483648)
        self.assertEqual(0b11111111111111111111111111111111, 4294967295)
        # Ditto with a minus sign and parentheses
        self.assertEqual(-(0b10000000000000000000000000000000), -2147483648)
        self.assertEqual(-(0b11111111111111111111111111111111), -4294967295)
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(-0b10000000000000000000000000000000, -2147483648)
        self.assertEqual(-0b11111111111111111111111111111111, -4294967295)

        # Positive constants
        self.assertEqual(
            0b1000000000000000000000000000000000000000000000000000000000000000,
            9223372036854775808,
        )
        self.assertEqual(
            0b1111111111111111111111111111111111111111111111111111111111111111,
            18446744073709551615,
        )
        # Ditto with a minus sign and parentheses
        self.assertEqual(
            -(0b1000000000000000000000000000000000000000000000000000000000000000),
            -9223372036854775808,
        )
        self.assertEqual(
            -(0b1111111111111111111111111111111111111111111111111111111111111111),
            -18446744073709551615,
        )
        # Ditto with a minus sign and NO parentheses
        # This failed in Python 2.2 through 2.2.2 and in 2.3a1
        self.assertEqual(
            -0b1000000000000000000000000000000000000000000000000000000000000000,
            -9223372036854775808,
        )
        self.assertEqual(
            -0b1111111111111111111111111111111111111111111111111111111111111111,
            -18446744073709551615,
        )


if __name__ == "__main__":
    unittest.main()
