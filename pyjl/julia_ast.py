"""
    julia AST

    Helps with the conversion of Python's ast to Julia
"""
import ast
from typing import Any, Optional


######################################
############### Types ################
######################################
class AbstractType(ast.Expr):
    value: ast.expr
    extends: ast.expr
    ctx: ast.expr_context


class LetStmt(ast.Lambda):
    args: list[ast.expr]
    body: list[ast.expr]
    ctx: ast.expr_context


class JuliaModule(ast.Module):
    name: ast.Name
    body: list[ast.expr]
    ctx: ast.expr_context


class OrderedDict(ast.Dict):
    keys: list[ast.expr]
    values: list[ast.expr]
    annotation: ast.expr


class OrderedDictComp(ast.DictComp):
    key: ast.expr
    value: ast.expr
    generators: list[ast.comprehension]
    annotation: ast.expr


class OrderedSet(ast.Set):
    elts: list[ast.expr]
    annotation: ast.expr


class Block(ast.FunctionDef):
    name: str
    block_expr: Optional[ast.expr]
    args: ast.arguments
    body: list[ast.expr]
    returns: ast.expr
    decorator_list: list[ast.expr]
    block_type: str
    ctx: ast.expr_context


class Constructor(ast.FunctionDef):
    name: str
    args: ast.arguments
    body: list[ast.expr]
    returns: ast.expr
    ctx: ast.expr_context


class Symbol(ast.Name):
    id: str


# Julia lambdas allows multiline functions,
# whereas Python's equivalent construct
# does not does not
class JuliaLambda(ast.FunctionDef):
    name: str  # Should always be None
    args: ast.arguments
    body: list[ast.expr]
    returns: ast.expr
    ctx: ast.expr_context


class InlineFunction(ast.FunctionDef):
    name: str
    args: ast.arguments
    body: list[ast.expr]  # Restriction: Only first element is evaluated
    returns: ast.expr  # By default, is empty
    ctx: ast.expr_context


######################################
############### Parser ###############
######################################


class JuliaNodeVisitor(ast.NodeVisitor):
    def visit_AbstractType(self, node: AbstractType) -> Any:
        """Visit abstract type node."""
        self.visit(node.value)
        self.visit(node.extends)
        return node

    def visit_LetStmt(self, node: LetStmt) -> Any:
        """Visit Julia let statement"""
        self.visit_Lambda(node)
        return node

    def visit_JuliaModule(self, node: JuliaModule) -> Any:
        """Visit Julia Module (a wrapper arround ast.Module)"""
        self.visit_Module(node)
        return node

    def visit_OrderedDict(self, node: OrderedDict) -> Any:
        """Visit Julia Ordered Dictionary (maintain the insertion order)"""
        for k in node.keys:
            self.visit(k)
        for v in node.values:
            self.visit(v)
        return node

    def visit_OrderedDictComp(self, node: OrderedDictComp) -> Any:
        """Visit Julia Ordered Dictionary (maintain the insertion order)"""
        self.visit(node.key)
        self.visit(node.value)
        for g in node.generators:
            self.visit(g)
        return node

    def visit_OrderedSet(self, node: OrderedSet) -> Any:
        """Visit Julia Ordered Sets (maintain the insertion order)"""
        for e in node.elts:
            self.visit(e)
        return node

    def visit_Block(self, node: Block) -> Any:
        """Visit Julia Block"""
        self.visit_FunctionDef(node)
        return node

    def visit_Constructor(self, node: Constructor) -> Any:
        """Visit Julia Constructor"""
        self.visit_FunctionDef(node)
        return node

    def visit_Symbol(self, node: Symbol) -> Any:
        """Visit Julia Symbol"""
        self.visit_Name(node)
        return node

    def visit_JuliaLambda(self, node: JuliaLambda) -> Any:
        """Visit Julia lambda"""
        self.visit_FunctionDef(node)
        return node

    def visit_InlineFunction(self, node: InlineFunction) -> Any:
        """Visit Julia inline function"""
        self.visit_FunctionDef(node)
        return node


class JuliaNodeTransformer(JuliaNodeVisitor):
    def __init__(self) -> None:
        super().__init__()
