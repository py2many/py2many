import ast
from typing import List

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstClassUsedBeforeDeclaration

from .clike import CLikeTranspiler
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
        self._needs_float_to_string = False
        self._dict_vars: set = set()  # Track variables assigned from dict/DictComp

    def indent(self, code, level=1):
        return self._indent * level + code

    def visit_Module(self, node) -> str:
        # Each top-level def trails a newline so consecutive defs are separated
        # by a blank line; trim the surrounding blanks since Lean has no
        # formatter to do it for us (ignored imports leave a leading blank, and
        # the cli re-appends a single trailing newline).
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
        lookup = MODULE_DISPATCH_TABLE.get(module_name, module_name)
        return f"import {lookup}"

    def _mutable_param_bindings(self, node) -> List[str]:
        """Emit ``let mut arg := arg`` for function params that are reassigned.

        Lean function parameters are immutable bindings.  When the Python
        source mutates a parameter (detected by the mutability analysis),
        we shadow it with a mutable ``let mut`` at the top of the body.
        """
        bindings = []
        _, args = self.visit(node.args)
        for arg in args:
            if arg == "self":
                continue
            if is_mutable(node.scopes, arg):
                bindings.append(
                    self.indent(f"let mut {arg} := {arg}", level=node.level + 1)
                )
                self._bound_vars.add(arg)
        return bindings

    def visit_FunctionDef(self, node) -> str:
        # Save and restore _bound_vars per function scope
        saved_bound = self._bound_vars.copy()
        self._bound_vars = set()

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
        args_str = (" " + " ".join(args_list)) if args_list else ""

        # For methods, add the self parameter with the class type
        self_type = getattr(node, "self_type", None)
        if has_self and self_type:
            args_str = f" (self : {self_type})" + args_str

        # Prepend mutable-parameter shadow bindings
        mut_bindings = self._mutable_param_bindings(node)

        body_stmts = [
            self.indent(self.visit(n), level=node.level + 1) for n in node.body
        ]
        body_stmts = mut_bindings + body_stmts

        body = "\n".join(body_stmts)
        if not body.strip():
            body = self.indent("pure ()", level=node.level + 1)

        if _is_io_function(node):
            return_type = "IO Unit"
            intro = "do"
        elif node.returns:
            return_type = self._typename_from_annotation(node, attr="returns")
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

        self._bound_vars = saved_bound
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

    def _visit_AssignOne(self, node, target) -> str:
        value = self.visit(node.value)
        # Reassignment to an existing binding (subscript/attribute, or a name
        # already bound in this scope) uses `name := value`; the first binding
        # uses `let [mut] name := value`. A var that is mutated later must be
        # introduced with `let mut`.
        if isinstance(target, ast.Subscript):
            # Subscript assignment: seq[i] = val  ->  seq := seq.set i val
            list_name = self.visit(target.value)
            index = self.visit(target.slice)
            return f"{list_name} := {list_name}.set {index} {value}"
        if isinstance(target, ast.Attribute):
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
        return f"{target} := {target} {op} {val}"

    def visit_Break(self, node) -> str:
        return "break"

    def visit_Continue(self, node) -> str:
        return "continue"

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        raw_id = get_id(node.target) if hasattr(node, "target") else target
        is_reassign = raw_id in self._bound_vars
        if not is_reassign:
            self._bound_vars.add(raw_id)
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
            return f"return {self.visit(node.value)}"
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
        if not vargs:
            return f"{fname}.mk"
        args = ", ".join(vargs)
        return f"{{ {args} : {fname} }}"

    def visit_Call(self, node) -> str:
        fname = self.visit(node.func)
        fndef = node.scopes.find(fname)

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

        # Handle list.append: lst.append(val) -> lst := lst ++ [val]
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and node.args
        ):
            list_name = self.visit(node.func.value)
            val = self.visit(node.args[0])
            return f"{list_name} := {list_name} ++ [{val}]"

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
        out = f"if {test} then\n{body}"
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

    def visit_For(self, node) -> str:
        target = self.visit(node.target)
        it = self.visit(node.iter)
        body = "\n".join(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        return f"for {target} in {it} do\n{body}"

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

        fields_str = "\n".join(fields)
        if fields_str:
            struct_def = f"structure {node.name} where\n{fields_str}\n"
        else:
            struct_def = f"structure {node.name} where\n  mk ::\n"
        if getattr(node, "is_dataclass", False):
            struct_def += "  deriving BEq, Repr\n"

        method_defs = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                if b.name == "__init__":
                    continue
                b.self_type = node.name
                method_defs.append(self.visit(b))

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
            return "({} : Std.HashMap _ _)"
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

    def visit_Subscript(self, node) -> str:
        value = self.visit(node.value)
        index = self.visit(node.slice)
        return f"{value}[{index}]!"

    def visit_Index(self, node) -> str:
        return self.visit(node.value)

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

    def visit_DictComp(self, node) -> str:
        """Translate ``{k: v for target in iter [if cond]}``."""
        self._headers.add("import Std")
        if len(node.generators) != 1:
            return self.comment(
                f"dict comprehension with {len(node.generators)} generators unsupported"
            )
        gen = node.generators[0]
        target = self.visit(gen.target)
        iter_expr = self.visit(gen.iter)
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
            ": Std.HashMap _ _)"
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
        return s

    def visit_Global(self, node) -> str:
        return ""

    def visit_IfExp(self, node) -> str:
        test = self.visit(node.test)
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        return f"(if {test} then {body} else {orelse})"
