
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
    keywords: list[ast.keyword] # TODO: not used yet
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

class OrderedDict(ast.Dict):
    keys: list[expr]
    values: list[expr]

class OrderedSet(ast.Set):
    elts: list[expr]


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
        
    def visit_OrderedDict(self, node: OrderedDict) -> Any:
        """Visit Julia Ordered Dictionary (maintain the insertion order)"""
        for k in node.keys:
            self.visit(k)
        for v in node.valus:
            self.visit(v)
        return node

    def visit_OrderedSet(self, node: OrderedSet) -> Any:
        """Visit Julia Ordered Sets (maintain the insertion order)"""
        for e in node.elts:
            self.visit(e)
        return node