# Unit Tests
import ast
from typing import Callable, Dict, Tuple, Union
import unittest


class JuliaExternalModulePlugins:
    def visit_assertTrue(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        return f"@test {vargs[1]}"

    def visit_assertFalse(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        return f"@test !({vargs[1]})"

    def visit_assertEqual(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        val = vargs[2]
        if isinstance(node.args[2], ast.Name):
            node.args[2].preserve_keyword=True
            val = t_self.visit(node.args[2])
        return f"@test ({vargs[1]} == {val})"

    def visit_assertRaises(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        exception = vargs[1]
        func = vargs[2]
        values = ", ".join(vargs[3:])
        return f"@test_throws {exception} {func}({values})"

    def visit_assertIsInstance(t_self, node, vargs):
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        return f"@test isa({vargs[0]}, {vargs[1]})"

    def visit_assertRaisesRegex(t_self, node, vargs):
        # 1. Checks if exceptiuon was thrown
        # 2. "Tests that regex matches on the string representation
        # of the raised exception"
        # https://docs.python.org/3/library/unittest.html#unittest.TestCase.assertRaisesRegex
        JuliaExternalModulePlugins._generic_test_visit(t_self)
        exception = vargs[1]
        regex = vargs[2]
        func = vargs[3]
        values = ", ".join(vargs[3:])
        return f"""
            @test_throws {exception} {func}({values})
            @test match(@r_str({regex}), repr({func}))"""

    def _generic_test_visit(t_self):
        t_self._usings.add("Test")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    unittest.TestCase.assertTrue: (JuliaExternalModulePlugins.visit_assertTrue, True),
    unittest.TestCase.assertFalse: (JuliaExternalModulePlugins.visit_assertFalse, True),
    unittest.TestCase.assertEqual: (JuliaExternalModulePlugins.visit_assertEqual, True),
    unittest.TestCase.assertRaises: (
        JuliaExternalModulePlugins.visit_assertRaises,
        True,
    ),
    unittest.TestCase.assertIsInstance: (
        JuliaExternalModulePlugins.visit_assertIsInstance,
        True,
    ),
    unittest.TestCase.assertRaisesRegex: (
        JuliaExternalModulePlugins.visit_assertRaisesRegex,
        True,
    ),
}
