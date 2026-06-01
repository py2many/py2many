import ast
from typing import List

from py2many.analysis import get_id, is_mutable, is_void_function
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

    def indent(self, code, level=1):
        return self._indent * level + code

    def visit_Module(self, node) -> str:
        # Each top-level def trails a newline so consecutive defs are separated
        # by a blank line; trim the surrounding blanks since Lean has no
        # formatter to do it for us (ignored imports leave a leading blank, and
        # the cli re-appends a single trailing newline).
        return super().visit_Module(node).strip("\n")

    def headers(self, meta=None):
        return "\n".join(sorted(self._headers))

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

    def visit_FunctionDef(self, node) -> str:
        body = "\n".join(
            [self.indent(self.visit(n), level=node.level + 1) for n in node.body]
        )
        if not body.strip():
            body = self.indent("pure ()", level=node.level + 1)

        # Python's `if __name__ == "__main__"` block is rewritten into a main()
        # function; Lean's runtime invokes `main : IO Unit` automatically, so no
        # explicit call site is emitted (unlike e.g. the Nim/Julia backends).
        if getattr(node, "python_main", False):
            return self.indent(f"def main : IO Unit := do\n{body}\n", level=node.level)

        typenames, args = self.visit(node.args)
        args_list = []
        for typename, arg in zip(typenames, args):
            if arg == "self":
                continue
            args_list.append(f"({arg} : {typename})")
        args_str = (" " + " ".join(args_list)) if args_list else ""

        if is_void_function(node):
            return_type = "IO Unit"
        elif node.returns:
            return_type = self._typename_from_annotation(node, attr="returns")
        else:
            return_type = "IO Unit"

        return self.indent(
            f"def {node.name}{args_str} : {return_type} := do\n{body}\n",
            level=node.level,
        )

    def visit_Assign(self, node) -> str:
        return "\n".join(
            [self._visit_AssignOne(node, target) for target in node.targets]
        )

    def _visit_AssignOne(self, node, target) -> str:
        value = self.visit(node.value)
        # Reassignment to an existing binding (subscript/attribute, or a name
        # already bound in this scope) uses `name := value`; the first binding
        # uses `let [mut] name := value`. A var that is mutated later must be
        # introduced with `let mut`.
        if isinstance(target, (ast.Subscript, ast.Attribute)):
            return f"{self.visit(target)} := {value}"
        if isinstance(target, ast.Tuple):
            elts = ", ".join([self.visit(e) for e in target.elts])
            return f"let ({elts}) := {value}"
        target_id = self.visit(target)
        kw = "let mut" if is_mutable(node.scopes, get_id(target)) else "let"
        return f"{kw} {target_id} := {value}"

    def visit_AugAssign(self, node) -> str:
        # Lean's do-notation has no compound-assignment operators; expand to a
        # plain reassignment (the target must have been bound with `let mut`).
        target = self.visit(node.target)
        op = self.visit(node.op)
        val = self.visit(node.value)
        return f"{target} := {target} {op} {val}"

    def visit_Break(self, node) -> str:
        return "break"

    def visit_Continue(self, node) -> str:
        return "continue"

    def visit_AnnAssign(self, node) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        if type_str == self._default_type:
            return f"let {target} := {val}"
        return f"let {target} : {type_str} := {val}"

    def visit_Return(self, node) -> str:
        if node.value:
            return f"return {self.visit(node.value)}"
        return "return"

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
        args = ", ".join(vargs)
        return f"{{ {args} : {fname} }}"

    def visit_Call(self, node) -> str:
        fname = self.visit(node.func)
        fndef = node.scopes.find(fname)

        if isinstance(fndef, ast.ClassDef):
            return self._visit_object_literal(node, fname, fndef)

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

    def visit_If(self, node) -> str:
        body = "\n".join(
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
        )
        test = self.visit(node.test)
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

    def visit_List(self, node) -> str:
        elements = ", ".join([self.visit(e) for e in node.elts])
        return f"[{elements}]"

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
