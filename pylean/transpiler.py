import ast
import re
from typing import List

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import (
    AstClassUsedBeforeDeclaration,
    AstCouldNotInfer,
    AstNotImplementedError,
    AstTypeNotSupported,
)
from py2many.inference import get_inferred_type

from .clike import CLikeTranspiler
from .inference import LEAN_WIDTH_RANK
from .plugins import (
    ATTR_DISPATCH_TABLE,
    DISPATCH_MAP,
    FUNC_DISPATCH_TABLE,
    FUNC_USINGS_MAP,
    MODULE_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)


def _is_recursive(node) -> bool:
    """Return True if the function calls itself (directly recursive)."""
    func_name = node.name
    for child in ast.walk(node):
        if isinstance(child, ast.Call):
            callee = None
            if isinstance(child.func, ast.Name):
                callee = child.func.id
            if callee == func_name:
                return True
    return False


def _is_io_function(node) -> bool:
    """Return True if a FunctionDef should be typed as IO.

    A function is IO when it is void (no return value) or when its body
    contains an IO call (IO.println, IO.Process.exit, etc.).  We also
    treat any function whose return annotation is missing as IO so that
    callers inside `do` blocks don't need a ← bind.
    """
    if is_void_function(node):
        return True
    if node.returns is None:
        return True
    return False


_INHABITED_BASE_TYPES = frozenset(
    {
        "Nat",
        "Int",
        "String",
        "Bool",
        "Float",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "Int8",
        "Int16",
        "Int32",
        "Int64",
    }
)
_INHABITED_CONTAINER_HEADS = ("List ", "Option ", "Array ")


def _has_negative_int(node) -> bool:
    """True when an expression contains a negative integer literal."""
    if node is None:
        return False
    for child in ast.walk(node):
        if isinstance(child, ast.UnaryOp) and isinstance(child.op, ast.USub):
            operand = child.operand
            if (
                isinstance(operand, ast.Constant)
                and isinstance(operand.value, int)
                and not isinstance(operand.value, bool)
            ):
                return True
    return False


def _fn_returns_int(fn: ast.FunctionDef, int_fns: set) -> bool:
    """True when an ``-> int`` function needs Lean ``Int``: it returns a
    negative literal, or returns a call to an Int-returning function. Nested
    definitions keep their own returns."""
    if get_id(getattr(fn, "returns", None)) != "int":
        return False
    stack = list(fn.body)
    while stack:
        stmt = stack.pop()
        if isinstance(
            stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
        ):
            continue
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            if _has_negative_int(stmt.value):
                return True
            call = stmt.value
            if (
                isinstance(call, ast.Call)
                and isinstance(call.func, ast.Name)
                and call.func.id in int_fns
            ):
                return True
        stack.extend(ast.iter_child_nodes(stmt))
    return False


def _lean_field_default(typename) -> str | None:
    """Zero value for a Lean field type (mirrors Python dataclass defaults).

    Returns None when no static default exists (custom structs without an
    Inhabited instance, proposition fields); callers leave those to fail
    loudly rather than inventing values.
    """
    if not isinstance(typename, str):
        return None
    if typename in ("Nat", "Int"):
        return "0"
    if typename in ("String",):
        return '""'
    if typename in ("Bool",):
        return "false"
    if typename in ("Float",):
        return "0.0"
    if typename.startswith(("List ", "Option ", "Array ")):
        head = typename.split(" ", 1)[0]
        if head == "List":
            return "[]"
        if head == "Option":
            return "none"
        return "#[]"
    if typename in _INHABITED_BASE_TYPES:
        return f"(default : {typename})"
    return None


def _find_annotated(scopes, name):
    """First annotated binding for ``name`` in enclosing scopes (or None).

    Scope lookup returns the innermost binding, which for reassigned
    variables is often an unannotated branch-local target shadowing the
    annotated declaration; this scans for one that carries a type.
    """
    for scope in reversed(scopes):
        for attr in ("vars", "body_vars", "orelse_vars"):
            for var in getattr(scope, attr, []):
                if get_id(var) == name:
                    ann = getattr(var, "annotation", None)
                    if ann is not None:
                        return ann
    return None


def _all_fields_inhabited(declarations, inhabited_structs=()) -> bool:
    """True when every field type is inhabited from core types.

    Plain types must be in a fixed set (or a struct that already derived an
    instance, passed via ``inhabited_structs``); ``List``/``Option``/``Array``
    are inhabited for any element type. Anything else is conservatively False.
    """
    if not declarations:
        return False
    for typename in declarations.values():
        if not isinstance(typename, str):
            return False
        if typename in _INHABITED_BASE_TYPES:
            continue
        if typename in inhabited_structs:
            continue
        if typename.startswith(_INHABITED_CONTAINER_HEADS):
            continue
        return False
    return True


class LeanTranspiler(CLikeTranspiler):
    NAME = "lean"

    def __init__(self, indent=2):
        super().__init__()
        self._headers = set()
        self._indent = " " * indent
        CLikeTranspiler._default_type = "_"
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        self._func_usings_map = FUNC_USINGS_MAP
        # Track variables that have been bound with ``let`` so that
        # subsequent assignments to the same name emit bare ``:=``
        # instead of a new ``let``.
        self._bound_vars: set = set()
        # Counter for named if-branch hypotheses (if h1 : ...); reset per
        # function in visit_FunctionDef.
        self._hyp_count = 0
        # Structs that derived an Inhabited instance (source order); later
        # structs with fields of these types can derive one too.
        self._inhabited_structs: set = set()
        self._needs_float_to_string = False
        self._dict_vars: set = set()  # Track variables assigned from dict/DictComp
        # Element types to use for an empty ``Std.HashMap`` literal while a dict
        # comprehension's (empty) source dict is being rendered; see
        # ``_empty_dict_source_type``.
        self._empty_dict_type: str = ""
        # Invariant field names of the class whose method is currently being
        # emitted; used to discharge constructor proof obligations (#805).
        self._self_invariants: List[str] = []
        # Names of module-level dependent types (#804) and the local variables
        # bound to such a type, so their uses can unwrap the subtype via ``.val``.
        self._dependent_type_names: set = set()
        self._dependent_vars: set = set()
        # Method names that carry an ``smt_pre`` precondition (#805); calls to
        # them must supply a proof argument.
        self._precondition_methods: set = set()
        # ``Int``-typed parameters of the function being emitted.  Lean indexes
        # lists/arrays with ``Nat``, so an index that uses one of these must be
        # coerced with ``.toNat`` (loop variables and lengths are already
        # ``Nat`` and must not be coerced).
        self._int_params: set = set()
        # NOTE: _int_return_funcs is intentionally NOT initialised here.
        # visit_Module recomputes it per file, and the parent visit_Module
        # re-runs __init__ (via _reset) after that, which would wipe it.
        # See visit_Module.

    def indent(self, code, level=1):
        return self._indent * level + code

    def _collapse_union(self, type_str: str):
        """Collapse a spurious ``Union[...]`` return type to a single Lean type.

        py2many's return-type inference unions a function's declared annotation
        with the inferred type of each ``return`` expression.  When those are
        the same type spelled differently (the Python ``int`` and its mapped
        ``Int``), it produces ``Union[int, Int]`` even though both denote one
        Lean type.  Map every member and, if they collapse to a single type,
        use it; otherwise pick the widest so the value still fits.
        """
        if not type_str or "Union[" not in type_str:
            return type_str
        members = {
            self._map_type(tok)
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", type_str)
            if tok != "Union"
        }
        if len(members) == 1:
            return members.pop()
        return max(members, key=lambda t: LEAN_WIDTH_RANK.get(t, 0))

    def _int_return_funcs_or_empty(self) -> set:
        # visit_Module populates this per file; default to empty when
        # visiting fragments directly (e.g. in tests).
        return getattr(self, "_int_return_funcs", set()) or set()

    def _wide_int_return(self, node, type_str) -> str:
        # Widen ``Nat`` to ``Int`` for functions that return negative ``int``
        # literals (e.g. ``-1`` sentinels): ``Nat`` cannot hold them. The
        # type may still be spelled ``int`` here (mapped to ``Nat`` later).
        if type_str in ("Nat", "int"):
            if getattr(node, "name", "") in self._int_return_funcs_or_empty():
                return "Int"
        return type_str

    def visit_Module(self, node) -> str:
        # Each top-level def trails a newline so consecutive defs are separated
        # by a blank line; trim the surrounding blanks since Lean has no
        # formatter to do it for us (ignored imports leave a leading blank, and
        # the cli re-appends a single trailing newline).
        # Precompute Int-returning functions (negative `int` literals need
        # Lean ``Int``, not ``Nat``): fixpoint over the call graph so
        # callers and ``-> int`` locals inherit ``Int`` too. Single module
        # only; cross-module calls conservatively stay ``Nat``.
        self._int_return_funcs = set()
        changed = True
        while changed:
            changed = False
            for child in ast.walk(node):
                if (
                    isinstance(child, ast.FunctionDef)
                    and child.name not in self._int_return_funcs
                    and _fn_returns_int(child, self._int_return_funcs)
                ):
                    self._int_return_funcs.add(child.name)
                    changed = True
        return super().visit_Module(node).strip("\n")

    def headers(self, meta=None):
        self._headers.add("set_option linter.unusedVariables false")
        if self._needs_float_to_string:
            # Helper to format floats like Python (trim trailing zeros)
            self._headers.add(
                "def floatToString (f : Float) : String :=\n"
                "  let s := toString f\n"
                "  if s.contains (Char.ofNat 46) then\n"
                "    let trimmed := (s.dropEndWhile (· == Char.ofNat 48)).toString\n"
                '    if trimmed.endsWith "." then trimmed ++ "0" else trimmed\n'
                "  else s"
            )
        # imports must appear first in a Lean file
        imports = sorted([h for h in self._headers if h.startswith("import ")])
        rest = sorted([h for h in self._headers if not h.startswith("import ")])
        return "\n".join(imports + rest)

    def usings(self):
        return ""

    def aliases(self):
        return ""

    def comment(self, text):
        return f"-- {text}\n"

    def _import(self, name: str) -> str:
        return f"import {name}"

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        # Drop transpiler-marker imports like ``py2many.theorem`` — these are
        # not real Python modules, they are annotations recognised by py2many
        # and have no corresponding Lean library.
        if module_name in ("py2many.theorem", "py2many.smt", "py2many.spec"):
            return ""
        lookup = MODULE_DISPATCH_TABLE.get(module_name, module_name)
        return f"import {lookup}"

    def _get_theorem_name(self, node) -> str:
        """Return the decorator id for a function node, checking for @theorem."""
        for d in node.decorator_list:
            name = get_id(d)
            if name == "theorem":
                return "theorem"
        return None

    def _get_decorator_name(self, node, names: set) -> str:
        """Return the first matching decorator name from *names*, or None."""
        for d in node.decorator_list:
            name = get_id(d)
            if name in names:
                return name
        return None

    def _extract_decorator_string(self, node, decorator_name: str) -> str:
        """Extract a string argument from a decorator like ``@invariant('prop')``."""
        for d in node.decorator_list:
            if isinstance(d, ast.Call):
                fn = get_id(d.func)
                if fn == decorator_name and d.args:
                    val = d.args[0]
                    if isinstance(val, ast.Constant) and isinstance(val.value, str):
                        return val.value
        return None

    def _extract_by_tactic(self, node) -> str:
        """If ``@by('tactic')`` is present, return the tactic string."""
        return self._extract_decorator_string(node, "by")

    def _theorem_proposition(self, node, fn_body, bare=False) -> str:
        """Extract the proposition from a @theorem or @lemma function body.

        The body should contain a single ``return <expr>`` statement which
        expresses the property to prove.  Returns the Lean expression.

        ``bare=True`` (used for tactics like ``omega`` that operate on a bare
        linear-arithmetic Prop) omits the ``= true`` wrapper so the tactic is
        applied to the arithmetic proposition itself rather than to a Bool
        equality, which ``omega`` cannot reduce.
        """
        # If body is a single return, use the return expression directly
        if len(fn_body) == 1 and isinstance(fn_body[0], ast.Return):
            expr = fn_body[0].value
            if expr is not None:
                if bare:
                    return self.visit(expr)
                return f"({self.visit(expr)}) = true"
        # Otherwise, build the proposition from the full body
        body_lean = "\n".join(self.visit(s) for s in fn_body)
        return body_lean

    def _get_invariant_decorator(self, node) -> List[tuple]:
        """Collect invariants from @invariant decorators on a class.

        Returns ``[(field_name, prop_str), ...]`` matching the format
        of ``_extract_invariants`` so the same emission path is reused.
        """
        props = []
        used: set = set()
        for d in node.decorator_list:
            if isinstance(d, ast.Call):
                fn = get_id(d.func)
                if fn == "invariant" and d.args:
                    val = d.args[0]
                    if isinstance(val, ast.Constant) and isinstance(val.value, str):
                        prop = val.value
                        # Derive field name from the first identifier in the prop
                        base = "inv"
                        for tok in prop.split():
                            if tok.isidentifier() and tok not in (
                                "not",
                                "and",
                                "or",
                                "=",
                                "!=",
                            ):
                                base = f"inv_{tok}"
                                break
                        name = base
                        suffix = 2
                        while name in used:
                            name = f"{base}_{suffix}"
                            suffix += 1
                        used.add(name)
                        props.append((name, prop))
        return props

    def _field_mutated_params(self, node, args) -> set:
        """Params mutated through a field: ``p.f = ...``, ``p.f[i] = ...``,
        ``p.f.append(...)``. The plain mutability analysis only sees bare
        name reassignments, so field writes need their own walk (nested
        function/class bodies keep their own scope and are skipped)."""
        params = set(args)
        mutated = set()
        stack = list(node.body)
        while stack:
            s = stack.pop()
            if isinstance(
                s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
            ):
                continue
            if isinstance(s, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                targets = s.targets if isinstance(s, ast.Assign) else [s.target]
                for t in targets:
                    root = t
                    while isinstance(root, ast.Subscript):
                        root = root.value
                    if isinstance(root, ast.Attribute) and isinstance(
                        root.value, ast.Name
                    ):
                        if root.value.id in params:
                            mutated.add(root.value.id)
            if (
                isinstance(s, ast.Call)
                and isinstance(s.func, ast.Attribute)
                and s.func.attr in ("append", "extend")
            ):
                root = s.func.value
                while isinstance(root, ast.Subscript):
                    root = root.value
                if isinstance(root, ast.Attribute) and isinstance(root.value, ast.Name):
                    if root.value.id in params:
                        mutated.add(root.value.id)
            stack.extend(ast.iter_child_nodes(s))
        return mutated

    def _mutable_param_bindings(self, node) -> List[str]:
        """Emit ``let mut arg := arg`` for function params that are reassigned.

        Lean function parameters are immutable bindings.  When the Python
        source mutates a parameter (detected by the mutability analysis),
        we shadow it with a mutable ``let mut`` at the top of the body.
        """
        bindings = []
        _, args = self.visit(node.args)
        field_mutated = self._field_mutated_params(node, args)
        for arg in args:
            if arg == "self":
                continue
            if arg in field_mutated or is_mutable(node.scopes, arg):
                bindings.append(
                    self.indent(f"let mut {arg} := {arg}", level=node.level + 1)
                )
                self._bound_vars.add(arg)
        return bindings

    def visit_FunctionDef(self, node) -> str:
        # Save and restore _bound_vars per function scope
        saved_bound = self._bound_vars.copy()
        self._bound_vars = set()
        saved_dep = self._dependent_vars.copy()
        self._dependent_vars = set()
        saved_int_params = self._int_params
        self._int_params = set()
        self._hyp_count = 0

        # Check for @theorem and @by decorators
        # Check for @theorem / @lemma and decorators
        decor_keyword = self._get_decorator_name(node, {"theorem", "lemma"})
        by_tactic = self._extract_by_tactic(node)

        # Python's `if __name__ == "__main__"` block is rewritten into a main()
        # function; Lean's runtime invokes `main : IO Unit` automatically, so no
        # explicit call site is emitted (unlike e.g. the Nim/Julia backends).
        if getattr(node, "python_main", False):
            # Bind ``args`` only when ``sys.argv`` is used, so other programs
            # keep the plain ``def main : IO Unit`` signature.
            uses_argv = any(
                isinstance(n, ast.Attribute)
                and n.attr == "argv"
                and get_id(n.value) == "sys"
                for n in ast.walk(node)
            )
            signature = "main (args : List String)" if uses_argv else "main"
            body_stmts = [
                self.indent(self.visit(n), level=node.level + 1) for n in node.body
            ]
            body = "\n".join(body_stmts)
            if not body.strip():
                body = self.indent("pure ()", level=node.level + 1)
            self._bound_vars = saved_bound
            self._dependent_vars = saved_dep
            self._int_params = saved_int_params
            return self.indent(
                f"def {signature} : IO Unit := do\n{body}\n", level=node.level
            )

        typenames, args = self.visit(node.args)
        args_list = []
        has_self = False
        for typename, arg in zip(typenames, args):
            if arg == "self":
                has_self = True
                continue
            args_list.append(f"({arg} : {typename})")
            if typename == "Int":
                self._int_params.add(arg)
        args_str = (" " + " ".join(args_list)) if args_list else ""

        # For methods, add the self parameter with the class type
        self_type = getattr(node, "self_type", None)
        if has_self and self_type:
            args_str = f" (self : {self_type})" + args_str

        # Precondition (#805): a leading ``if smt_pre:`` becomes a proof
        # parameter and is dropped from the emitted body.  Record the method
        # name so call sites can supply the proof argument.
        precond, postcond, fn_body = self._extract_precondition(node)
        if precond:
            args_str += f" (pre : {precond})"
            self._precondition_methods.add(node.name)

        # Postcondition (#826): an ``if CHECKER.post:`` block constrains the
        # return value.  Inside the block, ``result`` names the return value
        # (Dafny-style); rewrite it to the Lean subtype binder ``r`` and emit
        # the return type as ``{ r : T // post }``.  Other names (``self``,
        # parameters) refer to the pre-call state, which is exactly what the
        # functional Lean translation keeps.  Each ``return`` is lifted into
        # the subtype with ``by simp``: simp closes definitional goals like
        # rfl does, and additionally discharges error-branch goals of the
        # common ``¬result.ok ∨ ...`` shape. Path-sensitive goals still need
        # interactive proof (see visit_Return).
        post = None
        if postcond and node.returns and re.search(r"\bresult\b", postcond):
            post = re.sub(r"\bresult\b", "r", postcond)
            ret_type = self._collapse_union(
                self._typename_from_annotation(node, attr="returns")
            )
            ret_type = self._wide_int_return(node, ret_type)
            # Parenthesise the proposition: without parens a post like
            # ``r = a = b`` or ``r = x > 0`` does not parse in Lean.
            return_type = f"{{ r : {ret_type} // ({post}) }}"
            # Flag every return in this function (including ones nested in
            # ifs/loops) so visit_Return lifts each into the subtype. Nested
            # function/class definitions keep their own returns. The subtype
            # is stashed too: lifted returns bind through ``let ret : T``
            # (robust against formatter line-wrapping), which needs the type.
            stack = list(fn_body)
            while stack:
                stmt = stack.pop()
                if isinstance(stmt, ast.Return) and stmt.value is not None:
                    stmt.post_return_var = True
                    stmt.post_return_type = return_type
                elif isinstance(
                    stmt,
                    (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda),
                ):
                    continue
                else:
                    stack.extend(ast.iter_child_nodes(stmt))

        # Prepend mutable-parameter shadow bindings
        mut_bindings = self._mutable_param_bindings(node)

        body_stmts = [self.indent(self.visit(n), level=node.level + 1) for n in fn_body]
        body_stmts = mut_bindings + body_stmts

        body = "\n".join(body_stmts)
        if not body.strip():
            body = self.indent("pure ()", level=node.level + 1)

        if _is_io_function(node):
            return_type = "IO Unit"
            intro = "do"
        elif node.returns:
            if not post:
                # With a postcondition the subtype ``{ r : T // post }`` has
                # already been computed above; keep it as the return type.
                return_type = self._collapse_union(
                    self._typename_from_annotation(node, attr="returns")
                )
                return_type = self._wide_int_return(node, return_type)
            # Pure functions with imperative body (loops, mutation) need
            # ``Id.run do``; simple single-expression bodies could omit
            # the ``do`` but using ``Id.run do`` uniformly is safe and
            # keeps the emitter simple.
            intro = "Id.run do"
        else:
            return_type = "IO Unit"
            intro = "do"

        # For methods, prefix name with class name for dot notation
        func_name = CLikeTranspiler._rename_keyword(node.name)
        if has_self and self_type:
            func_name = f"{self_type}.{CLikeTranspiler._rename_keyword(node.name)}"

        # Recursive functions on non-structural types need ``partial``
        partial = "partial " if _is_recursive(node) else ""

        # A pure function whose whole body is a single ``return`` is emitted as
        # a plain definition ``def f ... : T := expr`` rather than
        # ``Id.run do return expr``.  This is more idiomatic and, unlike a do
        # block, the formatter can freely wrap a long expression without
        # breaking Lean's indentation-sensitive ``do`` parsing.
        # Emit theorem, lemma, or def
        if decor_keyword:
            # Both ``@lemma`` and ``@theorem`` emit ``theorem``; the keyword
            # ``lemma`` was not yet available in Lean 4 v4.32.2.
            # ``omega`` closes a bare linear-arithmetic Prop; a ``= true`` Bool
            # wrapper is not a goal it can reduce, so pass ``bare=True`` for it.
            prop = self._theorem_proposition(node, fn_body, bare=(by_tactic == "omega"))
            tactic_block = by_tactic if by_tactic else body
            thm_str = f"{partial}theorem {func_name}{args_str} : {prop} := by"
            if by_tactic:
                # Single-line tactic (e.g. native_decide, omega)
                out = f"{thm_str}\n{self.indent(tactic_block, level=node.level + 1)}\n"
            else:
                # Multi-line proof from the transpiled body
                out = f"{thm_str}\n{tactic_block}\n"
            self._bound_vars = saved_bound
            self._dependent_vars = saved_dep
            self._int_params = saved_int_params
            return self.indent(out, level=node.level)

        if (
            not _is_io_function(node)
            and not mut_bindings
            and len(fn_body) == 1
            and isinstance(fn_body[0], ast.Return)
            and fn_body[0].value is not None
        ):
            expr = self.visit(fn_body[0].value)
            if post:
                # Lift the single return expression into the postcondition
                # subtype ``{ r : T // post }``. simp_all discharges with
                # branch hypotheses; omega covers arithmetic residue.
                expr = (
                    f"⟨{expr}, by (try simp_all) <;> (first | omega | decide | grind)⟩"
                )
            self._bound_vars = saved_bound
            self._dependent_vars = saved_dep
            self._int_params = saved_int_params
            return self.indent(
                f"{partial}def {func_name}{args_str} : {return_type} := {expr}\n",
                level=node.level,
            )

        self._bound_vars = saved_bound
        self._dependent_vars = saved_dep
        self._int_params = saved_int_params
        return self.indent(
            f"{partial}def {func_name}{args_str} : {return_type} := {intro}\n{body}\n",
            level=node.level,
        )

    def visit_Assign(self, node) -> str:
        parts = [self._visit_AssignOne(node, target) for target in node.targets]
        if len(parts) == 1:
            return parts[0]
        # Multi-target assignment: join with proper indentation so that all
        # lines are at the same level when the parent calls indent().
        level = getattr(node, "level", 0)
        joiner = "\n" + self._indent * level
        return joiner.join(parts)

    def _is_module_scope(self, node) -> bool:
        """Return True when the assignment is at the top level of the module."""
        return hasattr(node, "scopes") and isinstance(node.scopes[-1], ast.Module)

    # Comparison operators rendered as Lean propositions (``Prop``) rather than
    # the boolean (``Bool``) operators used in ``if`` conditions: ``≤``/``≥``
    # instead of ``<=``/``>=`` and ``=`` instead of ``==``.
    _PROP_CMP_OPS = {
        ast.Lt: "<",
        ast.Gt: ">",
        ast.LtE: "≤",
        ast.GtE: "≥",
        ast.Eq: "=",
        ast.NotEq: "≠",
    }

    def _visit_proposition(self, node, class_name: str = None) -> str:
        """Render a Python boolean expression as a Lean ``Prop``.

        When *class_name* is given, dotted attribute references like
        ``BankAccount.balance`` are shortened to just ``balance`` so they
        work inside structure invariant fields where ``BankAccount`` is
        being defined.

        Differs from the ``Bool`` rendering used by ``if`` in two
        ways: ``and``/``or`` become ``∧``/``∨`` and Python's chained
        comparisons (``0 < x < 10``) expand to a conjunction
        (``0 < x ∧ x < 10``) since Lean has no chained relations.
        """
        if isinstance(node, ast.BoolOp):
            sym = "∧" if isinstance(node.op, ast.And) else "∨"
            return f" {sym} ".join(
                self._visit_proposition(v, class_name) for v in node.values
            )
        if isinstance(node, ast.Compare):
            clauses = []
            left = node.left
            for op, right in zip(node.ops, node.comparators):
                sym = self._PROP_CMP_OPS.get(type(op))
                if sym is None:
                    return self.visit(node)
                # Parenthesise nested boolean structure: Lean does not chain
                # relations, so ``r = a = b`` must render as ``(r) = (a = b)``.
                # Names and constants stay bare to avoid churning goldens.
                left_s = self._visit_proposition(left, class_name)
                if isinstance(left, (ast.Compare, ast.BoolOp)):
                    left_s = f"({left_s})"
                right_s = self._visit_proposition(right, class_name)
                if isinstance(right, (ast.Compare, ast.BoolOp)):
                    right_s = f"({right_s})"
                clauses.append(f"{left_s} {sym} {right_s}")
                left = right
            return " ∧ ".join(clauses)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return f"¬({self._visit_proposition(node.operand, class_name)})"
        # Strip class prefix from dotted names: ``BankAccount.balance`` → ``balance``
        if class_name and isinstance(node, ast.Attribute):
            val_id = get_id(node.value)
            names = class_name if isinstance(class_name, set) else {class_name}
            if val_id in names:
                return node.attr
        return self.visit(node)

    def _dependent_parts(self, value):
        """Return ``(base_type_node, lambda_node)`` for a dependent-type RHS.

        Recognises ``Annotated[T, lambda x: pred]`` and the alternative
        ``DependentType(T, lambda x: pred)`` spelling from #804.  Returns
        ``None`` when ``value`` is an ordinary assignment.
        """
        if isinstance(value, ast.Subscript):
            head = get_id(value.value) or ""
            if head.split(".")[-1] != "Annotated":
                return None
            sl = value.slice
            if isinstance(sl, ast.Index):  # py < 3.9 compatibility
                sl = sl.value
            if (
                isinstance(sl, ast.Tuple)
                and len(sl.elts) == 2
                and isinstance(sl.elts[1], ast.Lambda)
            ):
                return sl.elts[0], sl.elts[1]
            return None
        if (
            isinstance(value, ast.Call)
            and (get_id(value.func) or "").split(".")[-1] == "DependentType"
            and len(value.args) == 2
            and isinstance(value.args[1], ast.Lambda)
        ):
            return value.args[0], value.args[1]
        return None

    def _visit_dependent_type(self, name: str, value) -> str:
        """Emit a Lean subtype ``def Name := { x : T // pred }`` (#804)."""
        base_node, lam = self._dependent_parts(value)
        base = self._map_type(self.visit(base_node))
        binder = lam.args.args[0].arg
        pred = self._visit_proposition(lam.body)
        self._dependent_type_names.add(name)
        return f"def {name} := {{ {binder} : {base} // {pred} }}"

    def _extract_invariants(self, node) -> List[tuple]:
        """Collect ``(field_name, prop)`` from an ``if invariant:`` class block.

        Two styles are recognised inside the block:

        1. Bare expression: ``balance >= 0``
        2. Class method: ``def invariant(cls): return cls.balance >= 0``

        Both become a structure invariant field, e.g.
        ``inv_balance : balance ≥ 0``.
        """
        invariants: List[tuple] = []
        used: set = set()
        for stmt in node.body:
            if not (
                isinstance(stmt, ast.If) and self._checker_attr(stmt.test, "invariant")
            ):
                continue
            for inner in stmt.body:
                # Style 2: ``def invariant(cls): return expr``
                if isinstance(inner, ast.FunctionDef):
                    ret = inner.body[-1] if inner.body else None
                    if isinstance(ret, ast.Return) and ret.value is not None:
                        # The param (``cls`` / ``self``) is the class reference.
                        # We pass both the class name and the param name so
                        # _visit_proposition strips either prefix.
                        cls_param = inner.args.args[0].arg if inner.args.args else None
                        class_names = {node.name}
                        if cls_param:
                            class_names.add(cls_param)
                        prop = self._visit_proposition(ret.value, class_names)
                        base = "inv"
                        for sub in ast.walk(ret.value):
                            if isinstance(sub, ast.Attribute):
                                base = f"inv_{sub.attr}"
                                break
                        name = base
                        suffix = 2
                        while name in used:
                            name = f"{base}_{suffix}"
                            suffix += 1
                        used.add(name)
                        invariants.append((name, prop))
                    continue
                # Style 1: bare expression
                if not isinstance(inner, ast.Expr):
                    continue
                base = "inv"
                for sub in ast.walk(inner.value):
                    if isinstance(sub, ast.Attribute):
                        base = f"inv_{sub.attr}"
                        break
                    if isinstance(sub, ast.Name):
                        base = f"inv_{sub.id}"
                        break
                name = base
                suffix = 2
                while name in used:
                    name = f"{base}_{suffix}"
                    suffix += 1
                used.add(name)
                invariants.append(
                    (name, self._visit_proposition(inner.value, node.name))
                )
        return invariants

    @staticmethod
    def _checker_attr(node, attr: str) -> bool:
        """Return True when *node* is ``CHECKER.<attr>`` (dotted access).

        Also matches the plain-name form ``<attr>`` for backward compatibility
        with the older ``py2many.smt`` flat export.
        """
        if isinstance(node, ast.Attribute):
            return get_id(node.value) == "CHECKER" and node.attr == attr
        return get_id(node) == attr

    def _extract_precondition(self, node):
        """Split ``if CHECKER.pre:`` / ``if CHECKER.post:`` blocks off a function body.

        Returns ``(precondition_prop_or_None, postcondition_prop_or_None, body_without)``.
        The precondition becomes a proof parameter; the postcondition is a
        constraint on the return value.
        """
        pre = None
        post = None
        body = []
        for stmt in node.body:
            if isinstance(stmt, ast.If) and (
                self._checker_attr(stmt.test, "pre")
                or self._checker_attr(stmt.test, "smt_pre")
            ):
                preds = [
                    self._visit_proposition(s.value)
                    for s in stmt.body
                    if isinstance(s, ast.Expr)
                ]
                if preds:
                    pre = " ∧ ".join(preds)
                continue
            if isinstance(stmt, ast.If) and self._checker_attr(stmt.test, "post"):
                preds = [
                    self._visit_proposition(s.value)
                    for s in stmt.body
                    if isinstance(s, ast.Expr)
                ]
                if preds:
                    post = " ∧ ".join(preds)
                continue
            body.append(stmt)
        # Strip nested CHECKER blocks (e.g. inside loops/ifs): only top-level
        # blocks carry contract meaning; nested ones would otherwise leak
        # into the output since CheckerBlockRemover skips the Lean backend.
        body = [self._strip_nested_checker(s) for s in body]
        if post is not None:
            # Drop runtime asserts in post-carrying functions: ``assert!``
            # needs an Inhabited result, which postcondition subtypes lack.
            # The CHECKER pre/post pair subsumes these echoes (every assert
            # in the corpus mirrors a contract clause).
            body = [
                cleaned
                for s in body
                for cleaned in [self._strip_asserts(s)]
                if cleaned is not None
            ]
        return pre, post, body

    def _strip_asserts(self, node):
        """Remove ``assert`` statements under a node (nested defs keep theirs).

        Returns None when the node itself is an assert (caller drops it).
        """
        if isinstance(node, ast.Assert):
            return None
        if isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
        ):
            return node
        if not isinstance(node, ast.AST):
            return node
        for field, old in ast.iter_fields(node):
            if isinstance(old, list):
                kept = []
                for child in old:
                    if not isinstance(child, ast.AST):
                        kept.append(child)
                        continue
                    cleaned = self._strip_asserts(child)
                    if cleaned is not None:
                        kept.append(cleaned)
                setattr(node, field, kept)
            elif isinstance(old, ast.AST):
                setattr(node, field, self._strip_asserts(old))
        return node

    def _strip_nested_checker(self, node):
        """Remove nested ``if CHECKER.*:`` blocks under a statement.

        Nested definitions keep their own contracts; do not descend into
        them (their own _extract_precondition call handles those blocks).
        """
        if isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
        ):
            return node
        for field, old in ast.iter_fields(node):
            if isinstance(old, list):
                kept = []
                for child in old:
                    if not isinstance(child, ast.AST):
                        kept.append(child)
                        continue
                    if (
                        isinstance(child, ast.If)
                        and isinstance(child.test, ast.Attribute)
                        and isinstance(child.test.value, ast.Name)
                        and child.test.value.id == "CHECKER"
                    ):
                        continue
                    kept.append(self._strip_nested_checker(child))
                setattr(node, field, kept)
            elif isinstance(old, ast.AST):
                setattr(node, field, self._strip_nested_checker(old))
        return node

    def _struct_update(self, obj: str, attr: str, rhs: str) -> str:
        # Lean structures are immutable, so `obj.attr := rhs` rebinds the
        # whole owner. NOTE: the update is local to the enclosing do-block;
        # Python-style in-place mutation is not observable by callers unless
        # state is threaded explicitly (open follow-up for stateful code).
        return f"{obj} := {{ {obj} with {attr} := {rhs} }}"

    def _visit_AssignOne(self, node, target) -> str:
        # Dependent type aliases (#804): ``Uid = Annotated[int, lambda u: ...]``
        # become Lean subtypes.  Detected before visiting the RHS since the
        # generic expression visitors don't understand the predicate lambda.
        if (
            isinstance(target, ast.Name)
            and self._is_module_scope(node)
            and self._dependent_parts(node.value) is not None
        ):
            return self._visit_dependent_type(self.visit(target), node.value)

        value = self.visit(node.value)
        # Reassignment to an existing binding (subscript/attribute, or a name
        # already bound in this scope) uses `name := value`; the first binding
        # uses `let [mut] name := value`. A var that is mutated later must be
        # introduced with `let mut`.
        if isinstance(target, ast.Subscript):
            # Subscript assignment: seq[i] = val  ->  seq := seq.set i val.
            # A field subscript (store.items[i] = v) updates the whole owner.
            if isinstance(target.value, ast.Attribute) and isinstance(
                target.value.value, ast.Name
            ):
                obj = self.visit(target.value.value)
                # _index_str coerces Int indices (e.g. -1 sentinels) via
                # .toNat; a raw visit would leave Int where Nat is needed.
                index = self._index_str(target.slice)
                return self._struct_update(
                    obj,
                    target.value.attr,
                    f"{self.visit(target.value)}.set {index} {value}",
                )
            list_name = self.visit(target.value)
            index = self._index_str(target.slice)
            return f"{list_name} := {list_name}.set {index} {value}"
        if isinstance(target, ast.Attribute):
            # Field assignment mutates the owner: obj.f := v becomes the
            # functional update obj := { obj with f := v }.
            if isinstance(target.value, ast.Name):
                return self._struct_update(self.visit(target.value), target.attr, value)
            return f"{self.visit(target)} := {value}"
        if isinstance(target, ast.Tuple):
            elts = ", ".join([self.visit(e) for e in target.elts])
            return f"let ({elts}) := {value}"
        target_id = self.visit(target)
        raw_id = get_id(target)
        # Module-level (top-level) bindings use ``def`` in Lean 4
        if self._is_module_scope(node):
            return f"def {target_id} := {value}"
        if raw_id in self._bound_vars:
            # Already bound – bare reassignment
            return f"{target_id} := {value}"
        self._bound_vars.add(raw_id)
        kw = "let mut" if is_mutable(node.scopes, raw_id) else "let"
        # Add explicit type annotation when the type can be inferred from the
        # value (e.g., ``total = float(0.0)`` → ``let mut total : Float := 0.0``)
        # to help Lean's bidirectional type inference.
        type_hint = ""
        if isinstance(node.value, ast.Call):
            fname = get_id(node.value.func)
            if fname == "float":
                type_hint = " : Float"
        if isinstance(node.value, (ast.DictComp, ast.Dict)):
            type_hint = " : Std.HashMap _ _"
            self._dict_vars.add(raw_id)
        return f"{kw} {target_id}{type_hint} := {value}"

    def visit_AugAssign(self, node) -> str:
        # Lean's do-notation has no compound-assignment operators; expand to a
        # plain reassignment (the target must have been bound with `let mut`).
        if isinstance(node.target, ast.Subscript):
            # seq[i] += val  ->  seq := seq.set i (seq[i]! + val)
            list_name = self.visit(node.target.value)
            index = self.visit(node.target.slice)
            op = self.visit(node.op)
            val = self.visit(node.value)
            return f"{list_name} := {list_name}.set {index} ({list_name}[{index}]! {op} {val})"
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        # Handle Float/Nat mixing: if target is Float and value is Nat (or vice versa)
        target_type = CLikeTranspiler._get_node_type_id(node.target)
        val_type = CLikeTranspiler._get_node_type_id(node.value)
        target_is_float = target_type == "Float" or (
            isinstance(node.target, ast.Name)
            and not target_type
            and getattr(node.target, "annotation", None)
            and get_id(getattr(node.target, "annotation", None)) == "float"
        )
        val_is_float = val_type == "Float" or (
            isinstance(node.value, ast.Constant) and isinstance(node.value.value, float)
        )
        if target_is_float and not val_is_float:
            val = f"(Float.ofNat {val})"
        elif val_is_float and not target_is_float:
            target = f"(Float.ofNat {target})"
        if isinstance(node.op, ast.Add) and (
            self._is_str_val(node.target) or self._is_str_val(node.value)
        ):
            return f"{target} := {target} ++ {val}"
        return f"{target} := {target} {op} {val}"

    def visit_Break(self, node) -> str:
        return "break"

    def visit_Continue(self, node) -> str:
        return "continue"

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        raw_id = get_id(node.target) if hasattr(node, "target") else target
        # Widen ``Nat`` locals to ``Int`` when the value needs it (negative
        # literal, or a call to an Int-returning function); record them so
        # index and comparison sites can coerce (see _int_params).
        if type_str in ("Nat", "int") and isinstance(node.target, ast.Name):
            widen = _has_negative_int(node.value)
            if not widen and isinstance(node.value, ast.Call):
                widen = get_id(node.value.func) in self._int_return_funcs_or_empty()
            if widen:
                type_str = "Int"
                self._int_params.add(raw_id)
        is_reassign = raw_id in self._bound_vars
        if not is_reassign:
            self._bound_vars.add(raw_id)
        # Dependent-typed local (#804): build the subtype value ``⟨v, proof⟩``
        # and remember the binding so later uses unwrap it via ``.val``.
        if (
            type_str in self._dependent_type_names
            and val is not None
            and not self._is_module_scope(node)
        ):
            self._dependent_vars.add(raw_id)
            return f"let {target} : {type_str} := ⟨{val}, by omega⟩"
        # Module-level (top-level) bindings use ``def`` in Lean 4
        if self._is_module_scope(node):
            if val is None:
                if type_str == self._default_type:
                    return f"def {target} := default"
                return f"def {target} : {type_str} := default"
            if type_str == self._default_type:
                return f"def {target} := {val}"
            return f"def {target} : {type_str} := {val}"
        if is_reassign:
            if val is None:
                return f"{target} := default"
            return f"{target} := {val}"
        mutable = is_mutable(node.scopes, raw_id) if hasattr(node, "scopes") else False
        kw = "let mut" if mutable else "let"
        if val is None:
            if type_str == self._default_type:
                return f"{kw} {target} := default"
            return f"{kw} {target} : {type_str} := default"
        if type_str == self._default_type:
            return f"{kw} {target} := {val}"
        return f"{kw} {target} : {type_str} := {val}"

    def visit_Return(self, node) -> str:
        if node.value:
            rendered = self.visit(node.value)
            # Lift the returned value into the postcondition subtype
            # ``{ r : T // post }`` (see the tactic note above).
            if getattr(node, "post_return_var", False):
                rendered = f"⟨{rendered}, by (try simp_all) <;> (first | omega | decide | grind)⟩"
            # Sequence bracketed returns through ``let ret``: the formatter
            # may wrap a long ``return {...}`` line after ``return``, and
            # Lean then reads a bare ``return`` (``pure ()``) plus a stray
            # statement. ``;``-sequencing keeps one line; the formatter only
            # breaks it at safe points (after ``;`` or inside brackets).
            # The ``let`` carries the subtype ascription so ``⟨⟩`` elaborates
            # without an expected type from ``return``.
            if rendered.startswith(("{", "⟨", "({", "(⟨")):
                ret_type = getattr(node, "post_return_type", None)
                if ret_type is not None:
                    return f"let ret : {ret_type} := ({rendered}); return ret"
                return f"let ret := ({rendered}); return ret"
            return f"return {rendered}"
        return "return"

    def visit_Assert(self, node) -> str:
        test = self.visit(node.test)
        return f"assert! {test}"

    def visit_arg(self, node):
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = "_"
        if node.annotation:
            typename = self._typename_from_annotation(node)
        return (typename, id)

    def visit_Name(self, node) -> str:
        rendered = super().visit_Name(node)
        # A variable bound to a dependent type (#804) is a Lean subtype value;
        # unwrap it with ``.val`` wherever the underlying base value is used.
        if get_id(node) in self._dependent_vars:
            return f"{rendered}.val"
        return rendered

    def visit_Lambda(self, node) -> str:
        _, args = self.visit(node.args)
        args_str = " ".join(args)
        body = self.visit(node.body)
        return f"(fun {args_str} => {body})"

    def visit_Attribute(self, node) -> str:
        attr = node.attr
        # ``sys.argv``: Lean's ``main (args : List String)`` and the runtime omit
        # the program name (argv[0]), and ``lean --run`` exposes only ``args``.
        # Mirror the Julia/Nim backends, which prepend the program name, by
        # synthesising argv[0] from the module name so ``a[0]`` is populated.
        if get_id(node.value) == "sys" and attr == "argv":
            return f'(["{self._module}"] ++ args)'
        value_id = self.visit(node.value)
        if not value_id:
            value_id = ""
        ret = f"{value_id}.{attr}"
        if ret in self._attr_dispatch_table:
            return self._attr_dispatch_table[ret](self, node, value_id, attr)
        return ret

    def _visit_object_literal(self, node, fname: str, fndef: ast.ClassDef) -> str:
        vargs = []
        if not hasattr(fndef, "declarations"):
            raise AstClassUsedBeforeDeclaration(fndef, node)
        if node.args:
            for arg, decl in zip(node.args, fndef.declarations.keys()):
                vargs.append(f"{decl} := {self.visit(arg)}")
        if node.keywords:
            for kw in node.keywords:
                vargs.append(f"{kw.arg} := {self.visit(kw.value)}")
        # Fill fields the call omits (Python dataclass defaults): Lean
        # structures require every field. Invariant (proof) fields are
        # handled by the obligation loop below, so skip those here.
        given = set()
        if node.args:
            given.update(list(fndef.declarations.keys())[: len(node.args)])
        if node.keywords:
            given.update(kw.arg for kw in node.keywords)
        inv_names = {name for name, _ in getattr(fndef, "invariants", [])}
        for decl, typename in fndef.declarations.items():
            if decl in given or decl in inv_names:
                continue
            default = _lean_field_default(typename)
            if default is not None:
                vargs.append(f"{decl} := {default}")

        # Discharge invariant proof obligations (#805).  Bring the source
        # object's invariants (``self.inv_*``) into scope, then let ``omega``
        # close the goal.  This handles linear integer invariants; richer
        # predicates would need a more capable tactic or explicit proof reuse.
        invariants = getattr(fndef, "invariants", [])
        for inv_name, _prop in invariants:
            haves = "".join(
                f"have h{i} := self.{inv}; "
                for i, inv in enumerate(self._self_invariants)
            )
            vargs.append(f"{inv_name} := by {haves}omega")

        if not vargs:
            # Zero-argument construction (all dataclass defaults): Lean
            # structures have no defaults, so use the Inhabited default when
            # the struct declares fields (``deriving instance Inhabited`` is
            # emitted for eligible structs); a fieldless ``mk ::`` struct
            # uses its nullary constructor directly.
            if not getattr(fndef, "declarations", None):
                return f"{fname}.mk"
            return f"(default : {fname})"
        # Ascribe outside the braces: ``{ ... : T }`` misattaches the type
        # to the last field once the literal spans lines; ``({ ... } : T)``
        # is robust to formatter line-wrapping.
        args = ", ".join(vargs)
        return f"({{ {args} }} : {fname})"

    def visit_Call(self, node) -> str:
        fname = self.visit(node.func)
        fndef = node.scopes.find(fname)

        # ``prove(f)`` (demorgan2): prove that boolean function ``f`` holds for
        # all inputs via Lean's ``decide`` decision procedure -- the runnable
        # analogue of an SMT ``check-sat``.  Emitted as a ``have`` so the proof
        # is checked at compile time inside the enclosing ``do`` block.
        if isinstance(node.func, ast.Name) and node.func.id == "prove" and node.args:
            target = node.args[0]
            pname = get_id(target)
            pdef = node.scopes.find(pname)
            if isinstance(pdef, ast.FunctionDef):
                typenames, pargs = self.visit(pdef.args)
                params = [(t, a) for t, a in zip(typenames, pargs) if a != "self"]
                binders = " ".join(f"({a} : {t})" for t, a in params)
                app = " ".join([pname] + [a for _, a in params])
                quant = f"∀ {binders}, " if binders else ""
                return f"have _ : {quant}{app} = true := by decide"

        # ``check(claim)`` (equations2): verify that the values in scope satisfy
        # a constraint, the runnable analogue of an SMT model.  A call to a
        # boolean constraint function is discharged by evaluation (``decide``);
        # a bare linear-arithmetic proposition is discharged by ``omega``.
        if isinstance(node.func, ast.Name) and node.func.id == "check" and node.args:
            claim = node.args[0]
            if isinstance(claim, ast.Call):
                # Evaluate the boolean constraint function on the concrete model.
                # ``native_decide`` (compiled evaluation) handles list/array
                # indexing that the kernel ``decide`` cannot reduce.
                return f"have _ : {self.visit(claim)} = true := by native_decide"
            return f"have _ : {self._visit_proposition(claim)} := by omega"

        if isinstance(fndef, ast.ClassDef):
            return self._visit_object_literal(node, fname, fndef)

        # Handle sys.stdout.write / sys.stderr.write -> IO.print / IO.eprint
        # (Python's write does not append a newline, and neither does IO.print).
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "write"
            and isinstance(node.func.value, ast.Attribute)
            and get_id(node.func.value.value) == "sys"
            and node.func.value.attr in ("stdout", "stderr")
            and node.args
        ):
            arg = self.visit(node.args[0])
            fn = "IO.eprint" if node.func.value.attr == "stderr" else "IO.print"
            return f"({fn} {arg})"

        # Handle str.join: "sep".join(list) -> String.intercalate sep list
        if isinstance(node.func, ast.Attribute) and node.func.attr == "join":
            sep = self.visit(node.func.value)
            if node.args:
                arg = self.visit(node.args[0])
                if sep == '""':
                    return f"(String.join {arg})"
                return f"(String.intercalate {sep} {arg})"

        # Handle str.startswith/endswith/strip/lower/upper/split: map to
        # Lean core String functions (dot notation would emit unknown names).
        if isinstance(node.func, ast.Attribute) and node.func.attr in (
            "startswith",
            "endswith",
            "strip",
            "lower",
            "upper",
            "split",
        ):
            recv = self.visit(node.func.value)
            attr = node.func.attr
            if attr == "startswith" and node.args:
                return f"({recv}.startsWith {self.visit(node.args[0])})"
            if attr == "endswith" and node.args:
                return f"({recv}.endsWith {self.visit(node.args[0])})"
            if attr == "strip" and not node.args:
                return f"(String.trim {recv})"
            if attr == "lower" and not node.args:
                return f"(String.toLower {recv})"
            if attr == "upper" and not node.args:
                return f"(String.toUpper {recv})"
            if attr == "split" and node.args:
                return f"(String.splitOn {recv} {self.visit(node.args[0])})"
            # Fall through to default handling for arities we don't cover.

        # Handle list.append: lst.append(val) -> lst := lst ++ [val].
        # A field append (store.items.append(v)) updates the whole owner.
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and node.args
        ):
            list_name = self.visit(node.func.value)
            val = self.visit(node.args[0])
            if isinstance(node.func.value, ast.Attribute) and isinstance(
                node.func.value.value, ast.Name
            ):
                return self._struct_update(
                    self.visit(node.func.value.value),
                    node.func.value.attr,
                    f"{list_name} ++ [{val}]",
                )
            return f"{list_name} := {list_name} ++ [{val}]"
        # Handle list.extend: lst.extend(xs) -> lst := lst ++ xs
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "extend"
            and node.args
        ):
            list_name = self.visit(node.func.value)
            val = self.visit(node.args[0])
            return f"{list_name} := {list_name} ++ {val}"

        # Handle list.keys() and list.values()
        if isinstance(node.func, ast.Attribute) and node.func.attr == "keys":
            return f"({self.visit(node.func.value)}).toList.map Prod.fst"
        if isinstance(node.func, ast.Attribute) and node.func.attr == "values":
            return f"({self.visit(node.func.value)}).toList.map Prod.snd"

        vargs = []
        if node.args:
            vargs += [self.visit(a) for a in node.args]
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        # Supply the proof argument for a precondition method (#805).  ``omega``
        # discharges the concrete (linear integer) precondition at the call.
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr in self._precondition_methods
        ):
            vargs.append("(by omega)")
        # Same for standalone functions with @pre / @precondition
        if (
            isinstance(node.func, ast.Name)
            and node.func.id in self._precondition_methods
        ):
            vargs.append("(by omega)")

        ret = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret
        if vargs:
            # Lean uses juxtaposition for application: `f a b`.
            return f"({fname} {' '.join(vargs)})"
        return fname

    def _lean_condition(self, test_node) -> str:
        """Convert an arbitrary Python expression to a Lean Bool condition.

        Lean's ``if`` requires a ``Decidable`` proposition, not a bare Int
        or Nat.  When the test expression is a numeric Name or Constant we
        wrap it with ``!= 0`` so that ``if i:`` becomes ``if i != 0 then``.
        """
        test = self.visit(test_node)
        # Already a boolean-producing expression (comparison, bool op, etc.)
        if isinstance(
            test_node,
            (ast.Compare, ast.BoolOp, ast.UnaryOp),
        ):
            return test
        # Named constant True/False
        if isinstance(test_node, ast.Constant) and isinstance(test_node.value, bool):
            return test
        # A bare Name – check if it's a Bool variable first
        if isinstance(test_node, ast.Name):
            ann = getattr(test_node, "annotation", None)
            if ann and get_id(ann) == "bool":
                return test
            return f"{test} != 0"
        # A numeric literal or subscript – add truthiness check
        if isinstance(test_node, (ast.Constant, ast.Subscript)):
            return f"{test} != 0"
        # Call result – assume Bool, but if it's not we can't know without
        # type info; leave as is.
        return test

    def visit_If(self, node) -> str:
        # The ComplexDestructuringRewriter creates ``if True: <stmts>`` blocks
        # (with ``rewritten=True``) to wrap multi-statement expansions.  In
        # Lean we just emit the body statements directly. The first statement
        # inherits the parent's indentation; subsequent ones need explicit
        # indentation at the same level.
        if self.is_block(node):
            parts = [self.visit(c) for c in node.body]
            return ("\n" + self._indent * node.level).join(parts)

        body = "\n".join(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        test = self._lean_condition(node.test)
        # Name the branch condition: proofs (e.g. postcondition subtype
        # obligations) can then use it via simp_all/omega. Numbers are fresh
        # per function (reset in visit_FunctionDef).
        self._hyp_count += 1
        out = f"if h{self._hyp_count} : {test} then\n{body}"
        if node.orelse:
            orelse = "\n".join(
                [self.indent(self.visit(c), level=node.level + 1) for c in node.orelse]
            )
            out += f"\n{self.indent('else', level=node.level)}\n{orelse}"
        return out

    def visit_While(self, node) -> str:
        test = self.visit(node.test)
        body = "\n".join(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        return f"while {test} do\n{body}"

    def _is_str_iter(self, node) -> bool:
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return True
        if not isinstance(node, (ast.Name, ast.Attribute, ast.Subscript)):
            return False
        return get_id(get_inferred_type(node)) == "str"

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        if self._is_str_iter(node.iter):
            # Python iterates a String as 1-character strings; Lean yields
            # Char. Map through toString so the target stays a 1-character
            # String and all downstream string ops keep working unchanged.
            it = f"{it}.toList.map (fun c => toString c)"
        body = "\n".join(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        return f"for {target} in {it} do\n{body}"

    def _is_str_val(self, node) -> bool:
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return True
        if get_id(get_inferred_type(node)) == "str":
            return True
        # Branch-local reassignments (e.g. ``out += ...`` inside an if body)
        # shadow the annotated declaration in scope lookup; fall back to any
        # annotated binding of the same name in enclosing scopes.
        if isinstance(node, ast.Name) and hasattr(node, "scopes"):
            ann = _find_annotated(node.scopes, get_id(node))
            return get_id(ann) == "str"
        return False

    def _is_int_val(self, node) -> bool:
        # An Int-typed value: tracked Int local, negative literal, or call
        # to an Int-returning function. Plain ``int`` annotations stay Nat.
        if isinstance(node, ast.Name) and get_id(node) in self._int_params:
            return True
        if _has_negative_int(node):
            return True
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in self._int_return_funcs_or_empty()
        ):
            return True
        return False

    def _is_nat_val(self, node) -> bool:
        if (
            isinstance(node, ast.Constant)
            and isinstance(node.value, int)
            and not isinstance(node.value, bool)
            and node.value >= 0
        ):
            return True
        if isinstance(node, ast.Name) and node.id not in self._int_params:
            inferred = get_id(get_inferred_type(node))
            if inferred == "int":
                return True
        return False

    def visit_Compare(self, node) -> str:
        if len(node.ops) == 1 and isinstance(
            node.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)
        ):
            left, right = node.left, node.comparators[0]
            if self._is_str_val(left) or self._is_str_val(right):
                return super().visit_Compare(node)
            op = self.visit(node.ops[0])
            if self._is_int_val(left) and self._is_nat_val(right):
                return f"{self.visit(left)} {op} (({self.visit(right)}) : Int)"
            if self._is_int_val(right) and self._is_nat_val(left):
                return f"(({self.visit(left)}) : Int) {op} {self.visit(right)}"
        return super().visit_Compare(node)

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Add) and (
            self._is_str_val(node.left) or self._is_str_val(node.right)
        ):
            # Lean has no HAdd for String; string concatenation is Append.
            return f"({self.visit(node.left)} ++ {self.visit(node.right)})"
        return super().visit_BinOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(LeanTranspiler())
        extractor.visit(node)
        declarations = node.declarations = extractor.get_declarations()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        fields = []
        for declaration, typename in declarations.items():
            if typename is None:
                typename = "_"
            fields.append(f"  {declaration} : {typename}")

        # Class invariants (#805) become extra proposition-typed fields.
        # Merge invariants from ``if invariant:`` blocks and @invariant decorators.
        invariants = node.invariants = self._extract_invariants(node)
        decor_invariants = self._get_invariant_decorator(node)
        # Append decorator invariants, dedup by prop string
        seen_props = {p for _, p in invariants}
        for name, prop in decor_invariants:
            if prop not in seen_props:
                invariants.append((name, prop))
                seen_props.add(prop)
        for inv_name, prop in invariants:
            fields.append(f"  {inv_name} : {prop}")

        fields_str = "\n".join(fields)
        if fields_str:
            struct_def = f"structure {node.name} where\n{fields_str}\n"
        else:
            struct_def = f"structure {node.name} where\n  mk ::\n"
        # ``deriving BEq, Repr`` is only valid when every field is itself
        # BEq/Repr; proposition-typed invariant fields are not, so skip it.
        if getattr(node, "is_dataclass", False) and not invariants:
            struct_def += "  deriving BEq, Repr\n"
            # Indexing a list (``xs[i]!``) needs ``Inhabited`` element types.
            # Derive it when every field is inhabited from core types (plain
            # types from a fixed set, containers unconditionally); anything
            # exotic keeps today's behavior.
            if _all_fields_inhabited(declarations, self._inhabited_structs):
                struct_def += f"deriving instance Inhabited for {node.name}\n"
                self._inhabited_structs.add(node.name)

        method_defs = []
        # Expose the class's invariant field names so constructor calls inside
        # its methods can discharge the matching proof obligations from ``self``.
        saved_invariants = self._self_invariants
        self._self_invariants = [name for name, _ in invariants]
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                if b.name == "__init__":
                    continue
                b.self_type = node.name
                # Strip indentation — methods are top-level definitions in Lean
                method_defs.append(self.visit(b).lstrip())
        self._self_invariants = saved_invariants

        if method_defs:
            if len(method_defs) > 1:
                methods = "\nmutual\n" + "\n".join(method_defs) + "end\n"
            else:
                methods = "\n" + "\n".join(method_defs)
            return struct_def + methods
        return struct_def

    def _lean_enum_hashable(self, node_name, members):
        """Generate Hashable instance based on toNat for use in HashMap keys."""
        lines = []
        lines.append(f"instance : Hashable {node_name} where")
        lines.append("  hash v := hash v.toNat")
        lines.append("")
        return lines

    @staticmethod
    def _is_auto(var_node) -> bool:
        """Check if an AST node is an ``auto()`` call."""
        return isinstance(var_node, ast.Call) and get_id(var_node.func) == "auto"

    def visit_IntEnum(self, node) -> str:
        members = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            if self._is_auto(var):
                members.append((member, str(i + 1)))
            else:
                members.append((member, self.visit(var)))
        lines = [f"inductive {node.name} where"]
        for member, _ in members:
            lines.append(f"  | {member}")
        lines.append("  deriving BEq, Repr")
        lines.append("")
        lines.append(f"def {node.name}.toNat : {node.name} → Nat")
        for member, val in members:
            lines.append(f"  | .{member} => {val}")
        lines.append("")
        lines.extend(self._lean_enum_hashable(node.name, members))
        return "\n".join(lines)

    def visit_IntFlag(self, node) -> str:
        members = []
        for i, (member, var) in enumerate(node.class_assignments.items()):
            if self._is_auto(var):
                members.append((member, str(1 << i)))
            else:
                members.append((member, self.visit(var)))
        lines = [f"inductive {node.name} where"]
        for member, _ in members:
            lines.append(f"  | {member}")
        lines.append("  deriving BEq, Repr")
        lines.append("")
        lines.append(f"def {node.name}.toNat : {node.name} → Nat")
        for member, val in members:
            lines.append(f"  | .{member} => {val}")
        lines.append("")
        lines.extend(self._lean_enum_hashable(node.name, members))
        return "\n".join(lines)

    def visit_StrEnum(self, node) -> str:
        members = []
        for member, var in node.class_assignments.items():
            var = self.visit(var)
            members.append((member, var))
        lines = [f"inductive {node.name} where"]
        for member, _ in members:
            lines.append(f"  | {member}")
        lines.append("  deriving BEq, Repr")
        lines.append("")
        lines.append(f"def {node.name}.toString : {node.name} → String")
        for member, val in members:
            lines.append(f"  | .{member} => {val}")
        lines.append("")
        lines.append(f"instance : ToString {node.name} where")
        lines.append(f"  toString := {node.name}.toString")
        lines.append("")
        # For HashMap key support, we need Hashable
        lines.append(f"instance : Hashable {node.name} where")
        lines.append("  hash v := hash v.toString")
        lines.append("")
        return "\n".join(lines)

    def visit_List(self, node) -> str:
        elements = ", ".join([self.visit(e) for e in node.elts])
        return f"[{elements}]"

    def visit_Dict(self, node) -> str:
        self._headers.add("import Std")
        if not node.keys:
            return f"({{}} : {self._empty_dict_type or 'Std.HashMap _ _'})"
        # Build dict by chaining .insert calls
        result = "({} : Std.HashMap _ _)"
        for k, v in zip(node.keys, node.values):
            result = f"({result}.insert {self.visit(k)} {self.visit(v)})"
        return result

    def visit_Set(self, node) -> str:
        # Use a simple list-based set representation
        if not node.elts:
            return "([] : List _)"
        elts = ", ".join([self.visit(e) for e in node.elts])
        return f"[{elts}]"

    def visit_Tuple(self, node) -> str:
        elts = ", ".join([self.visit(e) for e in node.elts])
        if hasattr(node, "is_annotation"):
            return elts
        return f"({elts})"

    def _index_str(self, slice_node) -> str:
        """Render a list index, coercing ``Int`` parameters to ``Nat``.

        Lean indexes ``List``/``Array`` with ``Nat``.  Loop variables and
        lengths are already ``Nat``, but an index computed from an ``Int``
        parameter (e.g. ``board[row * 4 + col]``) needs an explicit ``.toNat``.
        """
        index = self.visit(slice_node)
        if any(
            isinstance(n, ast.Name) and get_id(n) in self._int_params
            for n in ast.walk(slice_node)
        ):
            return f"({index}).toNat"
        return index

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        # Handle slices: arr[:n] or arr[n:]
        if isinstance(node.slice, ast.Slice):
            return self.visit_Slice(node.slice, value)
        index = self._index_str(node.slice)
        return f"{value}[{index}]!"

    def visit_Index(self, node) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node, list_name=None) -> str:
        """Translate Python slices to Lean List.take / List.drop.

        ``arr[:n]``  → ``List.take n arr``
        ``arr[n:]``  → ``List.drop n arr``
        ``arr[:]``   → ``arr``
        """
        if list_name is None:
            return self.comment("Slice used as annotation -- unsupported")
        lower = self.visit(node.lower) if node.lower else None
        upper = self.visit(node.upper) if node.upper else None
        if lower is not None and upper is not None:
            # arr[lower:upper] → List.drop lower arr |>.take (upper - lower)
            return f"(List.drop {lower} {list_name} |>.take ({upper} - {lower}))"
        if lower is not None:
            # arr[lower:] → List.drop lower arr
            return f"(List.drop {lower} {list_name})"
        if upper is not None:
            # arr[:upper] → List.take upper arr
            return f"(List.take {upper} {list_name})"
        # arr[:]  identity
        return list_name

    def visit_Delete(self, node) -> str:
        parts = []
        for target in node.targets:
            if isinstance(target, ast.Subscript):
                name = self.visit(target.value)
                index = self.visit(target.slice)
                # For dicts: HashMap.erase; for lists: List.eraseIdx
                ann = getattr(target.value, "annotation", None)
                ann_id = get_id(ann) if ann else ""
                if ann_id and ("Dict" in str(ann_id) or "HashMap" in str(ann_id)):
                    parts.append(f"{name} := {name}.erase {index}")
                elif isinstance(ann, ast.Subscript):
                    val_id = get_id(ann.value) if hasattr(ann, "value") else ""
                    if val_id and ("Dict" in val_id or "dict" in val_id):
                        parts.append(f"{name} := {name}.erase {index}")
                    else:
                        parts.append(f"{name} := {name}.eraseIdx {index}")
                else:
                    parts.append(f"{name} := {name}.eraseIdx {index}")
            else:
                return self.comment(f"del unimplemented for {ast.dump(target)}")
        return "\n".join(parts)

    def visit_UnaryOp(self, node) -> str:
        if isinstance(node.op, ast.USub):
            operand = self.visit(node.operand)
            # Nat doesn't support negation; cast to Int
            op_type = CLikeTranspiler._get_node_type_id(node.operand)
            if op_type == "Nat":
                return f"(-(Int.ofNat {operand}))"
            if op_type in CLikeTranspiler._SIGNED_FW:
                return f"(-({operand}))"
            if op_type in CLikeTranspiler._UNSIGNED_FW:
                return f"(-(Int.ofNat {operand}.toNat))"
            if op_type == "Float":
                return f"(-({operand}))"
            # Untyped variable (e.g., inferred Nat from integer literal)
            if not op_type and isinstance(node.operand, ast.Name):
                return f"(-(Int.ofNat {operand}))"
            # Constant integer
            if isinstance(node.operand, ast.Constant) and isinstance(
                node.operand.value, int
            ):
                return f"(-(Int.ofNat {operand}))"
            return f"(-({operand}))"
        return f"{self.visit(node.op)}({self.visit(node.operand)})"

    def visit_ListComp(self, node) -> str:
        """Translate ``[elt for target in iter]`` and
        ``[elt for target in iter if cond]``."""
        if len(node.generators) != 1:
            return self.comment(
                f"list comprehension with {len(node.generators)} generators unsupported"
            )
        gen = node.generators[0]
        target = self.visit(gen.target)
        iter_expr = self.visit(gen.iter)
        elt = self.visit(node.elt)

        # Simple identity comprehension: [i for i in range(n)] -> List.range n
        if elt == target and not gen.ifs:
            return iter_expr

        # Build: iter |>.filter cond |>.map (fun target => elt)
        result = iter_expr
        for if_clause in gen.ifs:
            cond = self.visit(if_clause)
            result = f"({result}).filter (fun {target} => {cond})"
        if elt != target:
            result = f"({result}).map (fun {target} => {elt})"
        return result

    def _empty_dict_source_type(self, node) -> str:
        """Element types for a dict comprehension over an *empty* dict literal.

        Such a comprehension iterates nothing, so Lean's bidirectional inference
        only ever sees ``acc.insert <key> <value>``. When those expressions are
        themselves polymorphic -- ``key + 1`` matches ``HAdd`` against several
        instances -- Lean resolves the hole to a default that doesn't fit and
        the file fails to elaborate ("failed to synthesize HAdd PUnit Nat").
        Ascribe the types py2many inferred for the key/value expressions
        instead. Returns "" when they aren't known, leaving the ``_ _`` holes.
        """
        gen = node.generators[0]
        if not (isinstance(gen.iter, ast.Dict) and not gen.iter.keys):
            return ""
        key_type = self._optional_typename(node.key)
        value_type = self._optional_typename(node.value)
        if not (key_type and value_type):
            return ""
        return f"Std.HashMap {key_type} {value_type}"

    def _optional_typename(self, node) -> str:
        """Lean type name for ``node`` if py2many inferred one, else ""."""
        if getattr(node, "annotation", None) is None:
            return ""
        try:
            return self._typename_from_annotation(node) or ""
        except (AstCouldNotInfer, AstTypeNotSupported, AstNotImplementedError):
            return ""

    def visit_DictComp(self, node) -> str:
        """Translate ``{k: v for target in iter [if cond]}``."""
        self._headers.add("import Std")
        if len(node.generators) != 1:
            return self.comment(
                f"dict comprehension with {len(node.generators)} generators unsupported"
            )
        gen = node.generators[0]
        target = self.visit(gen.target)
        dict_type = self._empty_dict_source_type(node) or "Std.HashMap _ _"
        previous, self._empty_dict_type = self._empty_dict_type, dict_type
        try:
            iter_expr = self.visit(gen.iter)
        finally:
            self._empty_dict_type = previous
        key = self.visit(node.key)
        value = self.visit(node.value)

        # Build the source list (apply filters if any)
        # If the source is a dict/HashMap, use .toList first; lists don't need it
        is_dict_source = isinstance(gen.iter, ast.Dict)
        if not is_dict_source:
            ann = getattr(gen.iter, "annotation", None)
            if ann:
                ann_str = str(get_id(ann))
                is_dict_source = "Dict" in ann_str or "HashMap" in ann_str
        source = f"({iter_expr}).toList" if is_dict_source else iter_expr
        for if_clause in gen.ifs:
            cond = self.visit(if_clause)
            source = f"({source}).filter (fun {target} => {cond})"
        return (
            f"({source}).foldl (fun acc {target} => "
            f"acc.insert {key} {value}) "
            f"({{}}"
            f": {dict_type})"
        )

    def visit_Try(self, node, finallybody=None) -> str:
        level = getattr(node, "level", 0)
        body_parts = []
        for c in node.body:
            stmt = self.visit(c)
            # Wrap bare expressions (like `3 / 0`) in a throw to make them
            # compile in an IO try/catch block.  Pure expressions can't raise
            # Lean exceptions, so we wrap them with ``throwThe IO.Error``.
            if isinstance(c, ast.Expr) and isinstance(c.value, (ast.BinOp, ast.Call)):
                body_parts.append(self.indent(f"let _ := {stmt}", level=level + 1))
            else:
                body_parts.append(self.indent(stmt, level=level + 1))
        body = "\n".join(body_parts)
        buf = f"try\n{body}"
        for handler in node.handlers:
            handler.level = level
            buf += "\n" + self.indent(self.visit(handler), level=level)
        if node.finalbody:
            finally_body = "\n".join(
                [self.indent(self.visit(c), level=level + 1) for c in node.finalbody]
            )
            # Lean doesn't have finally; emit the body after the try/catch
            buf += "\n" + finally_body
        return buf

    def visit_ExceptHandler(self, node) -> str:
        level = getattr(node, "level", 0)
        if node.name:
            body = "\n".join(
                [self.indent(self.visit(c), level=level + 1) for c in node.body]
            )
            return f"catch {node.name} =>\n{body}"
        body = "\n".join(
            [self.indent(self.visit(c), level=level + 1) for c in node.body]
        )
        return f"catch _ =>\n{body}"

    def visit_Expr(self, node) -> str:
        s = self.visit(node.value)
        if not s:
            return ""
        # In a do block, bare expressions that aren't IO actions need
        # `let _ :=` to discard the value.  IO actions (IO.println etc.)
        # are fine as bare statements.
        if isinstance(node.value, (ast.DictComp, ast.ListComp, ast.SetComp)):
            return f"let _ := {s}"
        # A call whose return value is discarded (e.g. ``trim_searches(...)``
        # for effect): ``let _ :=`` unless the callee returns nothing.
        if isinstance(node.value, ast.Call):
            fndef = node.scopes.find(get_id(node.value.func))
            if isinstance(fndef, ast.FunctionDef) and fndef.returns is not None:
                return f"let _ := {s}"
        return s

    def visit_Global(self, node) -> str:
        return ""

    def visit_IfExp(self, node) -> str:
        test = self.visit(node.test)
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        return f"(if {test} then {body} else {orelse})"
