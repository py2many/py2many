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


class MatchExprDesugar(ast.NodeTransformer):
    """Rewrite spy-ast match expressions into CPython-compatible code.

    The new syntax::

        value = match x:
            1: "one"
            _: "other"

    is not valid CPython (where ``match`` is a statement), so each
    ``Match`` node in expression position becomes a nested ``IfExp`` chain::

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
