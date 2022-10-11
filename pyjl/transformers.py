import ast
from typing import Any

from py2many.ast_helpers import get_id


def parse_decorators(node, extension=False):
    visitor = JuliaDecoratorTransformer()
    visitor.visit(node)


class JuliaDecoratorTransformer(ast.NodeTransformer):
    """Parses decorators and adds them to functions
    and class scopes"""

    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def _parse_decorators(self, node):
        parsed_decorators: dict[str, dict[str, str]] = {}
        if decorator_list := getattr(node, "decorator_list", None):
            for decorator in decorator_list:
                if isinstance(decorator, ast.Name) or isinstance(
                    decorator, ast.Attribute
                ):
                    parsed_decorators[get_id(decorator)] = None
                elif isinstance(decorator, ast.Call):
                    keywords = {}
                    for keyword in decorator.keywords:
                        if hasattr(keyword.value, "value"):
                            keywords[keyword.arg] = keyword.value.value
                        else:
                            keywords[keyword.arg] = keyword.value
                    parsed_decorators[get_id(decorator.func)] = keywords

        if "dataclass" in parsed_decorators and "jl_dataclass" in parsed_decorators:
            parsed_decorators.pop("dataclass")

        node.parsed_decorators = parsed_decorators
