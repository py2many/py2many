
"""
    juliaAst

    Helps with the conversion of Python's ast to Julia
"""

from ast import AST, NodeVisitor, expr, expr_context, iter_fields, stmt
from typing import Any

######################################
############### Types ################
######################################

class AbstractType(stmt):
    value: expr
    extends: expr
    ctx: expr_context

class JuliaClass(stmt):
    name: expr
    bases: expr
    keywords: list[expr]
    body: list[expr]
    decorator_list: list[expr]
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

    def visit_JuliaClass(self, node: JuliaClass) -> Any:
        """Visit Julia class node."""
        method = 'visit_' + node.__class__.__name__
        visitor = getattr(self, method, self.generic_visit)
        return visitor(node)

    