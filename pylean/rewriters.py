import ast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node


class LeanWalrusRewriter(ast.NodeTransformer):
    """Hoist walrus (:=) expressions into separate assignments.

    Lean's ``do`` blocks support ``let`` bindings but not assignment inside
    an expression.  This rewriter extracts ``(x := expr)`` occurrences
    into ``let x := expr`` statements placed before the enclosing
    statement, then replaces the walrus with a bare reference to ``x``.
    """

    def _has_walrus(self, node):
        return any(isinstance(n, ast.NamedExpr) for n in ast.walk(node))

    def visit_Module(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_If(self, node):
        node.body = self._expand_body(node.body)
        node.orelse = self._expand_body(node.orelse)
        self.generic_visit(node)
        return node

    def visit_While(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_For(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def _expand_body(self, body):
        if not body:
            return body
        new_body = []
        for stmt in body:
            if not self._has_walrus(stmt):
                new_body.append(stmt)
                continue

            assignments = []

            class WalrusExtractor(ast.NodeTransformer):
                def visit_NamedExpr(self, named_expr):
                    named_expr.value = self.visit(named_expr.value)
                    assignments.append(
                        ast.Assign(
                            targets=[named_expr.target],
                            value=named_expr.value,
                            lineno=named_expr.lineno,
                            col_offset=getattr(named_expr, "col_offset", 0),
                        )
                    )
                    return named_expr.target

            extractor = WalrusExtractor()

            if isinstance(stmt, ast.While) and self._has_walrus(stmt.test):
                new_test = extractor.visit(stmt.test)
                break_if = ast.If(
                    test=ast.UnaryOp(op=ast.Not(), operand=new_test),
                    body=[ast.Break()],
                    orelse=[],
                    lineno=stmt.lineno,
                    col_offset=getattr(stmt, "col_offset", 0),
                )
                stmt.test = ast.Constant(value=True, lineno=stmt.lineno)
                stmt.body = assignments + [break_if] + stmt.body
                ast.fix_missing_locations(stmt)
                new_body.append(stmt)
            else:
                if isinstance(stmt, ast.If):
                    stmt.test = extractor.visit(stmt.test)
                elif isinstance(stmt, ast.For):
                    stmt.iter = extractor.visit(stmt.iter)
                elif hasattr(stmt, "value"):
                    stmt.value = extractor.visit(stmt.value)
                elif hasattr(stmt, "test"):
                    stmt.test = extractor.visit(stmt.test)
                ast.fix_missing_locations(stmt)
                new_body.extend(assignments)
                new_body.append(stmt)

        return new_body


class LeanImplicitConstructor(ast.NodeTransformer):
    """Give plain classes an explicit empty __init__ so the backend can emit a
    structure constructor, mirroring the other backends."""

    def visit_ClassDef(self, node):
        needs_init = "dataclass" not in [get_id(n) for n in node.decorator_list]
        for b in node.body:
            if isinstance(b, ast.FunctionDef) and b.name == "__init__":
                needs_init = False

        if not needs_init:
            return node

        new_node = create_ast_node("def __init__(self): pass")
        ast.fix_missing_locations(new_node)
        node.body.insert(0, new_node)
        return node
