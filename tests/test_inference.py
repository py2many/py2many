import ast
import unittest

from py2many.inference import infer_types, infer_types_typpete


def parse(*args):
    return ast.parse("\n".join(args))


class TestInference:
    def test_infer_types(self):
        tree = parse("a = [10, 20]")
        assert not hasattr(tree.body[0].targets[0], "annotation")
        infer_types(tree)
        assert hasattr(tree.body[0].targets[0], "annotation")
        assert tree.body[0].targets[0].annotation.value.id == "List"
        assert tree.body[0].targets[0].annotation.slice.id == "int"


class TestInferenceTyppete(unittest.TestCase):
    def test_infer_types_list_failure(self):
        tree = parse("a = [10, 20]")
        with self.assertRaises(AttributeError):
            infer_types_typpete(tree)
        # TODO: This should be true; c.f. non-typpete test
        # assert hasattr(tree.body[0].targets[0], "annotation")

    def test_infer_types_print_exception(self):
        tree = parse("print(10)")
        with self.assertRaises(AttributeError):
            infer_types_typpete(tree)
