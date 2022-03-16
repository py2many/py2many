
"""
    juliaAst

    Helps with the conversion of Python's ast to Julia
"""

from ast import NodeVisitor, expr, expr_context, stmt
import ast
from typing import Any

######################################
############### Types ################
######################################


class AbstractType(stmt):
    value: expr
    extends: expr
    ctx: expr_context

class Constructor(stmt):
    struct_name: ast.Name
    args: ast.arguments
    body: list[expr]
    ctx: expr_context

######################################
############### Parser ###############
######################################


class JuliaNodeVisitor(NodeVisitor):

    def visit_AbstractType(self, node: AbstractType) -> Any:
        """Visit abstract type node."""
        method = 'visit_' + node.__class__.__name__
        visitor = getattr(self, method, self.generic_visit)
        return visitor(node)

    def visit_Constructor(self, node: Constructor) -> Any:
        """Visit Julia constructor"""
        method = 'visit_' + node.__class__.__name__
        visitor = getattr(self, method, self.generic_visit)
        return visitor(node)
