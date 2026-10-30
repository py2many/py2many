import spy_ast.ast as ast

from .ast_helpers import create_ast_node
from .clike import CLikeTranspiler


class RestoreMainRewriter(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        is_python_main = getattr(node, "python_main", False)

        if is_python_main:
            if_block = create_ast_node("if __name__ == '__main__': True", node)
            if_block.body = node.body
            ast.fix_missing_locations(if_block)
            return if_block
        return node


class MatchStmtLifter(ast.NodeTransformer):
    """Lower match expressions in statement position to match statements.

    The new syntax::

        kind = match code:
            43: PLUS
            _: -1

    is a match *expression*, but CPython only has match *statements*, so
    assignments, returns and bare matches over a ``Match`` node become the
    equivalent statement (CPython 3.10+)::

        match code:
            case 43:
                kind = PLUS
            case _:
                kind = -1

    The subject is evaluated once natively, so no temporary is needed.
    Matches nested in arm position lift recursively into nested match
    statements. Only int-literal patterns (``MatchValue``) and the wildcard
    (``MatchAs``) exist in the new syntax; anything else (e.g. named
    captures, which CPython would read as bindings) is a transpile-time
    error, as is a missing wildcard (falling through would leave the
    target unbound).
    """

    def _check_pattern(self, pattern, node):
        if isinstance(pattern, ast.MatchValue):
            return pattern
        if isinstance(pattern, ast.MatchAs) and pattern.pattern is None:
            if pattern.name not in (None, "_"):
                raise ValueError(f"match capture {pattern.name!r} not supported")
            return ast.MatchAs()
        raise ValueError(f"unsupported match pattern {pattern!r}")

    def _lift_match(self, node, make_stmt):
        cases = []
        has_wildcard = False
        for case in node.cases:
            pattern = self._check_pattern(case.pattern, node)
            if isinstance(pattern, ast.MatchAs):
                has_wildcard = True
            if len(case.body) == 1 and isinstance(case.body[0], ast.Expr):
                arm = case.body[0].value
            else:  # pragma: no cover - parser only emits single-expr arms
                raise ValueError("match arm body must be a single expression")
            # Visit the new statement (not the original arm): a match in
            # arm position lifts recursively into a nested match statement.
            lifted = self.visit(make_stmt(arm))
            body = lifted if isinstance(lifted, list) else [lifted]
            new_case = ast.match_case(pattern=pattern, guard=None, body=body)
            ast.copy_location(new_case, case)
            cases.append(new_case)
        if not has_wildcard:
            raise ValueError("match expression requires a catch-all `_` arm")
        stmt = ast.Match(subject=node.subject, cases=cases)
        ast.copy_location(stmt, node)
        ast.fix_missing_locations(stmt)
        # Mark lowered statements so MatchExprDesugar (next pass) leaves
        # them alone: their case bodies are statements, not expressions.
        stmt._match_stmt = True
        return stmt

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Match):
            return self._lift_match(
                node.value,
                lambda arm: ast.Assign(targets=node.targets, value=arm),
            )
        return self.generic_visit(node)

    def visit_Return(self, node):
        if isinstance(node.value, ast.Match):
            return self._lift_match(node.value, lambda arm: ast.Return(value=arm))
        return self.generic_visit(node)

    def visit_Expr(self, node):
        if isinstance(node.value, ast.Match):
            return self._lift_match(node.value, lambda arm: ast.Expr(value=arm))
        return self.generic_visit(node)


class MatchExprDesugar(ast.NodeTransformer):
    """Rewrite leftover match expressions into CPython-compatible code.

    ``MatchStmtLifter`` (which runs first) turns matches in statement
    position (assignments, returns, bare matches) into match statements.
    Any ``Match`` node left over -- nested inside a larger expression where
    no statement can go -- becomes a nested ``IfExp`` chain::

        "one" if x == 1 else "other"

    Non-trivial subjects (anything but a Name/Constant) are evaluated once
    via a walrus-bound temporary::

        "one" if (__match_subj_0 := f(y)) == 1 else "other"

    Only int-literal patterns (``MatchValue``) and the wildcard (``MatchAs``)
    exist in the new syntax. A missing wildcard is a transpile-time error:
    silently emitting ``None`` would change semantics, and an expression
    cannot ``raise``.
    """

    def __init__(self):
        self._counter = 0

    def visit_Match(self, node):
        if getattr(node, "_match_stmt", False):
            # Already lowered to a match statement by MatchStmtLifter;
            # recurse (arm expressions may hold nested expression matches)
            # but do not convert.
            self.generic_visit(node)
            return node
        self.generic_visit(node)
        subject = node.subject
        arms = []
        default = None
        for case in node.cases:
            pattern = case.pattern
            if len(case.body) == 1 and isinstance(case.body[0], ast.Expr):
                body = case.body[0].value
            else:  # pragma: no cover - parser only emits single-expr arms
                raise ValueError("match arm body must be a single expression")
            if isinstance(pattern, ast.MatchValue):
                if default is not None:
                    break  # unreachable: arms after the wildcard
                arms.append((pattern.value, body))
            elif isinstance(pattern, ast.MatchAs) and pattern.pattern is None:
                if pattern.name not in (None, "_"):
                    raise ValueError(f"match capture {pattern.name!r} not supported")
                if default is None:
                    default = body
            else:  # pragma: no cover - parser only emits the above
                raise ValueError(f"unsupported match pattern {pattern!r}")
        if default is None:
            raise ValueError("match expression requires a catch-all `_` arm")
        if isinstance(subject, (ast.Name, ast.Constant)):
            subject_exprs = [subject] * len(arms)
        else:
            tmp = ast.Name(id=f"__match_subj_{self._counter}", ctx=ast.Load())
            self._counter += 1
            first = ast.NamedExpr(
                target=ast.Name(id=tmp.id, ctx=ast.Store()), value=subject
            )
            ast.copy_location(first, subject)
            ast.copy_location(first.target, subject)
            subject_exprs = [first] + [tmp] * (len(arms) - 1)
        result = default
        for (literal, body), subj in zip(reversed(arms), reversed(subject_exprs)):
            test = ast.Compare(left=subj, ops=[ast.Eq()], comparators=[literal])
            ast.copy_location(test, node)
            result = ast.IfExp(test=test, body=body, orelse=result)
            ast.copy_location(result, node)
        ast.fix_missing_locations(result)
        return result


class PythonTranspiler(CLikeTranspiler):
    NAME = "python"

    def __init__(self, no_prologue: bool = False):
        super().__init__()
        CLikeTranspiler._type_map = {}
        CLikeTranspiler._container_type_map = {}
        self._no_prologue = no_prologue

    def visit(self, node):
        node = MatchStmtLifter().visit(node)
        node = MatchExprDesugar().visit(node)
        return ast.unparse(node)

    def usings(self):
        return (
            "\n".join(
                [
                    "from typing import Callable, Dict, List, Set, Optional",
                    "from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64",
                    "from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64",
                    "import sys",
                ]
            )
            if not self._no_prologue
            else ""
        )
