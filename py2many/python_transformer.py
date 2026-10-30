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
        if isinstance(pattern, ast.MatchClass):
            # Variant patterns (`Token.PLUS():`, `Expr.ADD(l, r):`):
            # cls must be `Name.Attr`, bindings must be names/`_`.
            cls = pattern.cls
            if not (isinstance(cls, ast.Attribute) and isinstance(cls.value, ast.Name)):
                raise ValueError(f"unsupported variant pattern {pattern!r}")
            for sub in list(pattern.patterns or []) + list(pattern.kwd_patterns or []):
                if not isinstance(sub, ast.MatchAs):
                    raise ValueError(f"unsupported variant binding {sub!r}")
                if sub.pattern is not None:
                    raise ValueError(f"unsupported variant binding {sub!r}")
            if getattr(pattern, "kwd_attrs", None):
                raise ValueError(f"keyword variant patterns not supported {pattern!r}")
            return pattern
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
            if isinstance(pattern, ast.MatchClass):
                # Variant patterns lower to `case _ if subj.is_variant():`
                # with accessor bindings prepended (works with adt, keeps
                # the `match` keyword instead of if/elif).
                cls = pattern.cls
                assert isinstance(cls, ast.Attribute) and isinstance(
                    cls.value, ast.Name
                )
                variant = cls.attr
                lower = variant.lower()
                subj = node.subject
                guard = ast.Call(
                    func=ast.Attribute(value=subj, attr=f"is_{lower}", ctx=ast.Load()),
                    args=[],
                    keywords=[],
                )
                ast.copy_location(guard.func, cls)
                ast.copy_location(guard, case)
                ast.fix_missing_locations(guard)
                bindings = []
                for sub in list(pattern.patterns or []):
                    if isinstance(sub, ast.MatchAs):
                        bindings.append(sub.name)
                    else:  # pragma: no cover - checked in _check_pattern
                        raise ValueError(f"unsupported variant binding {sub!r}")
                pre = []
                if len(bindings) == 1:
                    target = ast.Name(id=bindings[0], ctx=ast.Store())
                    ast.copy_location(target, case)
                    acc = ast.Call(
                        func=ast.Attribute(value=subj, attr=lower, ctx=ast.Load()),
                        args=[],
                        keywords=[],
                    )
                    ast.copy_location(acc, case)
                    assign = ast.Assign(targets=[target], value=acc)
                    ast.copy_location(assign, case)
                    pre.append(assign)
                elif len(bindings) > 1:
                    targets = [ast.Name(id=b, ctx=ast.Store()) for b in bindings]
                    for tg in targets:
                        ast.copy_location(tg, case)
                    tup_target = ast.Tuple(elts=targets, ctx=ast.Store())
                    ast.copy_location(tup_target, case)
                    acc = ast.Call(
                        func=ast.Attribute(value=subj, attr=lower, ctx=ast.Load()),
                        args=[],
                        keywords=[],
                    )
                    ast.copy_location(acc, case)
                    assign = ast.Assign(targets=[tup_target], value=acc)
                    ast.copy_location(assign, case)
                    pre.append(assign)
                body = pre + body
                new_case = ast.match_case(pattern=ast.MatchAs(), guard=guard, body=body)
            else:
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


class SealedDefaultFiller(ast.NodeTransformer):
    """Fill nullary sealed constructions with their defaults.

    `Token.PLUS()` where `PLUS: int = '+'` becomes `Token.PLUS('+')`
    so adt (which requires an arg for int payloads) keeps working.
    Payloads are never read (only `is_*` matters), so the exact
    default value is irrelevant as long as construction succeeds.
    """

    def _fresh_default(self, value):
        # Scope-free copy for simple defaults (avoids deepcopying the
        # whole scope tree, which hangs). Supports the defaults used
        # in the dialect fixture: string/int constants and ord('x').
        if isinstance(value, ast.Constant):
            return ast.Constant(value=value.value)
        if (
            isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id == "ord"
            and len(value.args) == 1
            and isinstance(value.args[0], ast.Constant)
            and not value.keywords
        ):
            return ast.Call(
                func=ast.Name(id="ord", ctx=ast.Load()),
                args=[ast.Constant(value=value.args[0].value)],
                keywords=[],
            )
        # Fallback for anything else: shallow-copy the node itself
        # without scopes (never deepcopy scoped trees).
        import copy as _copy_mod

        fresh = _copy_mod.copy(value)
        for attr in (
            "scopes",
            "_attributes",
            "lineno",
            "col_offset",
            "end_lineno",
            "end_col_offset",
        ):
            if hasattr(fresh, attr):
                try:
                    delattr(fresh, attr)
                except AttributeError:
                    pass
        return fresh

    def visit_Call(self, node):
        self.generic_visit(node)
        func = node.func
        if not (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)):
            return node
        if node.args or node.keywords:
            return node
        scopes = getattr(node, "scopes", None)
        if scopes is None:
            return node
        clsdef = scopes.find(func.value.id)
        if clsdef is None or not isinstance(clsdef, ast.ClassDef):
            return node
        if "sealed" not in [getattr(d, "id", None) for d in clsdef.decorator_list]:
            return node
        # Find default for this variant in class body AnnAssigns.
        for stmt in clsdef.body:
            if (
                isinstance(stmt, ast.AnnAssign)
                and getattr(stmt.target, "id", None) == func.attr
            ):
                if stmt.value is not None:
                    node.args = [self._fresh_default(stmt.value)]
                    ast.fix_missing_locations(node.args[0])
                    break
        return node


class SealedDefaultStripper(ast.NodeTransformer):
    """Strip defaults from sealed variant definitions for adt."""

    def visit_ClassDef(self, node):
        if "sealed" not in [getattr(d, "id", None) for d in node.decorator_list]:
            return self.generic_visit(node)
        for stmt in node.body:
            if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
                stmt.value = None
        return self.generic_visit(node)


class SealedParenVariantDesugar(ast.NodeTransformer):
    """Desugar paren-style sealed variants to Tuple annotations.

    The new syntax allows tuple variants to be declared with call-style::

        @sealed
        class Expr:
            NUMBER: float
            ADD(Expr, Expr)

    which is equivalent to ``ADD: Tuple["Expr", "Expr"]`` (the form the
    ``adt`` runtime understands). Self-references become string literals
    so the annotation does not evaluate the class under construction.
    Unit variants (``X: None``) and other annotations pass through.
    """

    def visit_ClassDef(self, node):
        if "sealed" not in [getattr(d, "id", None) for d in node.decorator_list]:
            return self.generic_visit(node)
        new_body = []
        for stmt in node.body:
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Name)
                and not stmt.value.keywords
            ):
                variant = stmt.value.func.id
                args = []
                for arg in stmt.value.args:
                    if isinstance(arg, ast.Name) and arg.id == node.name:
                        lit = ast.Constant(value=arg.id)
                        ast.copy_location(lit, arg)
                        args.append(lit)
                    else:
                        args.append(arg)
                tuple_elts = ast.Tuple(elts=args, ctx=ast.Load())
                ast.copy_location(tuple_elts, stmt.value)
                subscript = ast.Subscript(
                    value=ast.Name(id="Tuple", ctx=ast.Load()),
                    slice=tuple_elts,
                )
                ast.copy_location(subscript, stmt.value)
                ast.copy_location(subscript.value, stmt.value.func)
                target = ast.Name(id=variant, ctx=ast.Store())
                ast.copy_location(target, stmt.value.func)
                ann_assign = ast.AnnAssign(
                    target=target, annotation=subscript, simple=1
                )
                ast.copy_location(ann_assign, stmt)
                new_body.append(ann_assign)
            else:
                new_body.append(self.visit(stmt) if False else stmt)
        node.body = new_body
        # Visit remaining children (e.g. decorators) but not the converted
        # AnnAssigns (they hold no Match nodes).
        return node


class PythonTranspiler(CLikeTranspiler):
    NAME = "python"

    def __init__(self, no_prologue: bool = False):
        super().__init__()
        CLikeTranspiler._type_map = {}
        CLikeTranspiler._container_type_map = {}
        self._no_prologue = no_prologue

    def visit(self, node):
        node = SealedParenVariantDesugar().visit(node)
        node = SealedDefaultFiller().visit(node)
        node = SealedDefaultStripper().visit(node)
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
