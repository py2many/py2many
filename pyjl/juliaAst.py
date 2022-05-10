
"""
    juliaAst

    Helps with the conversion of Python's ast to Julia
"""

from ast import  NodeVisitor, expr, expr_context, stmt
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

class LetStmt(stmt):
    args: expr
    body: list[expr]
    ctx: expr_context

class JuliaModule(ast.Module):
    name: ast.Name
    body: list[expr]
    ctx: expr_context

######################################
############### Parser ###############
######################################

class JuliaNodeVisitor(NodeVisitor):

    def visit_AbstractType(self, node: AbstractType) -> Any:
        """Visit abstract type node."""
        self.visit(node.value)
        self.visit(node.extends)
        return node

    def visit_Constructor(self, node: Constructor) -> Any:
        """Visit Julia constructor"""
        self.visit(node.name)
        for a in node.args:
            self.visit(a)
        for n in node.body:
            self.visit(n)
        return node

    def visit_LetStmt(self, node: LetStmt) -> Any:
        """Visit Julia let statement"""
        for a in node.args:
            self.visit(a)
        for n in node.body:
            self.visit(n)
        return node

    def visit_JuliaModule(self, node: JuliaModule) -> Any:
        """Visit Julia Module (a wrapper arround ast.Module)"""
        self.visit_Module(node)
        return node
