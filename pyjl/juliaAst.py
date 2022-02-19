
"""
    juliaAst

    Helps with the conversion of Python's ast to Julia
"""

from ast import NodeVisitor, expr, expr_context, stmt
import ast
from typing import Any

_identifier = str

######################################
############### Types ################
######################################

class AbstractType(stmt):
    value: expr
    ctx: expr_context


######################################
############### Parser ###############
######################################

class JuliaNodeVisitor(NodeVisitor):

    def visit_AbstractType(self, node: AbstractType) -> Any:
        name = self.visit(node.value)
        return f"abstract type Abstract{name} end"

    