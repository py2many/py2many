import ast
import textwrap
from typing import Any, Optional, Union, cast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_block, create_ast_node
from py2many.astx import ASTxFunctionDef
from py2many.clike import CLikeTranspiler
from py2many.inference import get_inferred_type
from py2many.scope import ScopeList
from py2many.tracer import find_node_by_type


class InferredAnnAssignRewriter(ast.NodeTransformer):
    def visit_Assign(self, node):
        target = node.targets[0]  # Assumes all targets have same annotation
        if isinstance(target, ast.Subscript):
            return node
        annotation = getattr(target, "annotation", False)
        if not annotation:
            return node

        if isinstance(annotation, ast.ClassDef):
            annotation = ast.Name(id=get_id(annotation))

        col_offset = getattr(node, "col_offset", None)

        assigns = []
        for assign_target in node.targets:
            definition = node.scopes.parent_scopes.find(get_id(assign_target))
            if definition is None:
                definition = node.scopes.find(get_id(assign_target))
            if definition is not assign_target:
                previous_type = get_inferred_type(definition)
                if get_id(previous_type) == get_id(annotation):
                    if len(node.targets) == 1:
                        return node
                    else:
                        new_node = ast.Assign(
                            targets=[assign_target],
                            value=node.value,
                            lineno=node.lineno,
                            col_offset=col_offset,
                        )
                        assigns.append(new_node)
                        continue
            new_node = ast.AnnAssign(
                target=assign_target,
                value=node.value,
                lineno=node.lineno,
                col_offset=col_offset,
                simple=True,
                annotation=annotation,
            )
            assigns.append(new_node)

        if len(assigns) == 1:
            return assigns[0]

        return create_ast_block(body=assigns, at_node=node)


class DropClassGetItemRewriter(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        if node.name == "__class_getitem__":
            return None
        return node


class ComplexDestructuringRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._disable = False
        if language in {"cpp", "julia", "d", "dart", "v", "mojo"}:
            self._disable = True
        self._no_underscore = False
        if language in {"nim"}:
            self._no_underscore = True
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        if self._no_underscore:
            return f"tmp{self._temp}"
        return f"__tmp{self._temp}"

    def visit_Assign(self, node):
        if self._disable:
            return node
        target = node.targets[0]
        if isinstance(target, ast.Tuple) and not (isinstance(target.elts[0], ast.Name)):
            temps = []
            orig = [None] * len(target.elts)
            body = [node]
            for i in range(len(target.elts)):
                temps.append(ast.Name(id=self._get_temp(), lineno=node.lineno))
                # The irony!
                target.elts[i], orig[i] = temps[i], target.elts[i]
                body.append(
                    ast.Assign(targets=[orig[i]], value=temps[i], lineno=node.lineno)
                )
            return create_ast_block(body=body, at_node=node)
        return node


class RenameTransformer(ast.NodeTransformer):
    def __init__(self, old_name, new_name):
        super().__init__()
        self._old_name = old_name
        self._new_name = new_name

    def visit_Name(self, node):
        if node.id == self._old_name:
            node.id = self._new_name
        return node

    def visit_FunctionDef(self, node):
        if node.name == self._old_name:
            node.name = self._new_name
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name) and node.func.id == self._old_name:
            node.func.id = self._new_name
        self.generic_visit(node)
        return node


class WithToBlockTransformer(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language
        self._no_underscore = False
        if language in {"nim"}:
            self._no_underscore = True
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
        if self._no_underscore:
            return f"tmp{self._temp}"
        return f"__tmp{self._temp}"

    def visit_With(self, node):
        # v and python support `with` natively; lowering it to a plain block
        # drops the context manager's __exit__ (e.g. file close), which leaks
        # the handle and breaks os.remove on Windows.
        if self._language in ("python", "v"):
            return node
        self.generic_visit(node)
        stmts = []
        for i in node.items:
            if i.optional_vars:
                target = i.optional_vars
            else:
                target = ast.Name(id=self._get_temp(), lineno=node.lineno)
            stmt = ast.Assign(
                targets=[target], value=i.context_expr, lineno=node.lineno
            )
            stmts.append(stmt)
        node.body = stmts + node.body
        ret = create_ast_block(body=node.body, at_node=node)
        # Hint to UnpackScopeRewriter below to leave the new scope alone
        ret.unpack = False
        return ret


def capitalize_first(name):
    first = name[0].upper()
    remainder = list(name)
    remainder.remove(name[0])
    remainder = "".join(remainder)
    return first + remainder


def camel_case(name):
    if "_" not in name:
        return name
    # Dont rewrite dunders
    if name.startswith("__") and name.endswith("__"):
        return name
    return "".join(capitalize_first(part) if part else "" for part in name.split("_"))


def rename(scope, old_name, new_name):
    tx = RenameTransformer(old_name, new_name)
    tx.visit(scope)


class PythonMainRewriter(ast.NodeTransformer):
    def __init__(self, main_signature_arg_names):
        self.main_signature_arg_names = set(main_signature_arg_names)
        super().__init__()

    def visit_If(self, node):
        is_main = (
            isinstance(node.test, ast.Compare)
            and isinstance(node.test.left, ast.Name)
            and node.test.left.id == "__name__"
            and isinstance(node.test.ops[0], ast.Eq)
            and isinstance(node.test.comparators[0], ast.Constant)
            and node.test.comparators[0].value == "__main__"
        )
        if is_main:
            if hasattr(node, "scopes") and len(node.scopes) > 1:
                rename(node.scopes[-2], "main", "main_func")
            # ast.parse produces a Module object that needs to be destructured
            if self.main_signature_arg_names == {"argc", "argv"}:
                ret = cast(
                    ast.FunctionDef,
                    create_ast_node(
                        "def main(argc: int, argv: List[str]) -> int: True", node
                    ),
                )
            elif self.main_signature_arg_names == {"argv"}:
                ret = create_ast_node("def main(argv: List[str]): True", node)
            else:
                ret = create_ast_node("def main(): True")
            ret = cast(ASTxFunctionDef, ret)
            ret.lineno = node.lineno
            ret.body = node.body
            # So backends know to handle argc, argv etc
            ret.python_main = True
            return ret
        return node


class FStringJoinRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language

    def visit_JoinedStr(self, node):
        # mojo fstrings will be implemented at some point
        # https://github.com/modularml/mojo/issues/398
        if self._language in {"mojo", "python", "v"}:
            return node
        new_node = cast(ast.Expr, create_ast_node('"".join([])', node)).value
        new_node = cast(ast.Call, new_node)
        args = new_node.args
        arg0 = cast(ast.List, args[0])
        for v in node.values:
            if isinstance(v, ast.Constant):
                arg0.elts.append(v)
            elif isinstance(v, ast.FormattedValue):
                arg0.elts.append(
                    ast.Call(
                        func=ast.Name(id="str", ctx="Load"), args=[v.value], keywords=[]
                    )
                )
        new_node.lineno = node.lineno
        new_node.col_offset = node.col_offset
        ast.fix_missing_locations(new_node)
        return new_node


class DocStringToCommentRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._docstrings = set()
        self._docstring_parent = {}

    def _get_doc_node(self, node) -> Optional[ast.AST]:
        if not (node.body and isinstance(node.body[0], ast.Expr)):
            return None
        node = node.body[0].value
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node
        return None

    def _visit_documentable(self, node):
        doc_node = self._get_doc_node(node)
        self._docstrings.add(doc_node)
        self._docstring_parent[doc_node] = node
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node):
        return self._visit_documentable(node)

    def visit_ClassDef(self, node):
        return self._visit_documentable(node)

    def visit_Module(self, node):
        return self._visit_documentable(node)

    def visit_Constant(self, node):
        if node in self._docstrings:
            parent = self._docstring_parent[node]
            parent.docstring_comment = ast.Constant(value=node.value)
            return None
        return node

    def visit_Expr(self, node):
        self.generic_visit(node)
        if not hasattr(node, "value"):
            return None
        return node


class PrintBoolRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language

    def _do_other_rewrite(self, node) -> ast.AST:
        ifexpr = cast(
            ast.Expr, create_ast_node("'True' if true else 'False'", node)
        ).value
        ifexpr = cast(ast.IfExp, ifexpr)
        ifexpr.test = node.args[0]
        ifexpr.lineno = node.lineno
        ifexpr.col_offset = node.col_offset
        ast.fix_missing_locations(ifexpr)
        node.args[0] = ifexpr
        return node

    # Go can't handle IfExpr in print. Handle it differently here
    def _do_go_rewrite(self, node) -> ast.AST:
        if_stmt = create_ast_node(
            textwrap.dedent(
                """\
            if True:
                print('True')
            else:
                print('False')
        """
            ),
            node,
        )
        if_stmt = cast(ast.If, if_stmt)
        if_stmt.test = node.args[0]
        if_stmt.lineno = node.lineno
        if_stmt.col_offset = node.col_offset
        ast.fix_missing_locations(if_stmt)
        return if_stmt

    def visit_Call(self, node):
        if get_id(node.func) == "print":
            if len(node.args) == 1:
                anno = getattr(node.args[0], "annotation", None)
                if get_id(anno) == "bool":
                    if self._language == "go":
                        return self._do_go_rewrite(node)
                    else:
                        return self._do_other_rewrite(node)
        return node


class StrStrRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language

    def visit_Compare(self, node):
        if self._language in {"d", "dart", "kotlin", "nim", "python"}:
            return node

        if isinstance(node.ops[0], ast.In):
            left = node.left
            right = node.comparators[0]
            left_type = get_id(get_inferred_type(left))
            right_type = get_id(get_inferred_type(right))
            if left_type == "str" and right_type == "str":
                if self._language == "julia":
                    ret = ast.parse("findfirst(a, b) != Nothing").body[0].value
                    ret.left.args[0] = left
                    ret.left.args[1] = right
                elif self._language == "go":
                    # To be rewritten to strings.Contains via plugins
                    ret = ast.parse("StringsContains(a, b)").body[0].value
                    ret.args[0] = right
                    ret.args[1] = left
                elif self._language == "cpp":
                    ret = ast.parse("a.find(b) != string.npos").body[0].value
                    ret.left.func.value = right
                    ret.left.args[0] = left
                else:
                    # rust and c++23
                    ret = ast.parse("a.contains(b)").body[0].value
                    ret.func.value = right
                    ret.args[0] = left
                ret.lineno = node.lineno
                ast.fix_missing_locations(ret)
                return ret

        return node


class IgnoredAssignRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language
        self._disable = language in {"lean", "nim", "v"}
        self._unpack = language in {"cpp", "d", "dart", "go", "rust"}

    def _visit_assign_unpack_all(self, node):
        keep_ignored = self._language == "go"
        body = []
        target = node.targets[0]
        for i in range(len(target.elts)):
            elt = target.elts[i]
            if isinstance(elt, ast.Name):
                name = get_id(elt)
                if name == "_" and not keep_ignored:
                    body.append(ast.Expr(value=node.value.elts[i]))
                    body[-1].unused = True
                    continue
            body.append(ast.Assign(targets=[target.elts[i]], value=node.value.elts[i]))
        return create_ast_block(body=body, at_node=node)

    def visit_Assign(self, node):
        if self._disable:
            return node

        target = node.targets[0]
        if isinstance(target, ast.Tuple) and isinstance(node.value, ast.Tuple):
            names = [get_id(elt) for elt in target.elts if isinstance(elt, ast.Name)]
            has_ignored = "_" in names
            if self._unpack and has_ignored:
                return self._visit_assign_unpack_all(node)
            if not has_ignored:
                return node

            body = [node]
            to_eval = []
            for i in range(len(target.elts)):
                if names[i] == "_":
                    del target.elts[i]
                    to_eval.append(node.value.elts[i])
                    del node.value.elts[i]
            # TODO: Evaluation order - we may have to split the tuple assignment to get
            # it right. For now, keep it simple
            body = [ast.Expr(value=e) for e in to_eval] + body
            return create_ast_block(body=body, at_node=node)
        return node


class UnpackScopeRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._language = language

    def _visit_body(self, body):
        unpacked = []
        for s in body:
            do_unpack = getattr(s, "unpack", True)
            if isinstance(s, ast.If) and CLikeTranspiler.is_block(s) and do_unpack:
                unpacked.extend(self._visit_body(s.body))
            else:
                unpacked.append(s)
        return unpacked

    def _visit_assign_node_body(self, node):
        node.body = self._visit_body(node.body)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> ast.FunctionDef:
        return self._visit_assign_node_body(node)

    def visit_For(self, node: ast.For) -> ast.For:
        return self._visit_assign_node_body(node)

    def visit_If(self, node: ast.If) -> ast.If:
        return self._visit_assign_node_body(node)

    def visit_With(self, node: ast.With) -> ast.With:
        return self._visit_assign_node_body(node)

    def visit_While(self, node: ast.With) -> ast.With:
        return self._visit_assign_node_body(node)


class LoopElseRewriter(ast.NodeTransformer):
    def __init__(self, language) -> None:
        super().__init__()
        self._language = language
        self._has_break_var_name = "has_break"

    def visit_Module(self, node: ast.Module) -> Any:
        self._visit_Scope(node)
        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._visit_Scope(node)
        return node

    def visit_If(self, node: ast.If) -> Any:
        self._visit_Scope(node)
        return node

    def visit_With(self, node: ast.With) -> Any:
        self._visit_Scope(node)
        return node

    def visit_For(self, node: ast.For) -> Any:
        self._generic_loop_visit(node)
        self._visit_Scope(node)
        return node

    def visit_While(self, node: ast.While) -> Any:
        self._generic_loop_visit(node)
        self._visit_Scope(node)
        return node

    def _generic_loop_visit(self, node: Union[ast.For, ast.While]):
        scopes = getattr(node, "scopes", ScopeList())
        if len(node.orelse) > 0:
            lineno = node.orelse[0].lineno
            if_expr = ast.If(
                test=ast.Compare(
                    left=ast.Name(id=self._has_break_var_name),
                    ops=[ast.NotEq()],
                    comparators=[ast.Constant(value=True)],
                ),
                body=[oe for oe in node.orelse],
                orelse=[],
                lineno=lineno,
            )
            # Manually set scopes attribute after construction
            if_expr.test.scopes = scopes
            if_expr.test.comparators[0].scopes = scopes
            node.if_expr = if_expr

    def _visit_Scope(self, node) -> Any:
        self.generic_visit(node)
        scopes = getattr(node, "scopes", ScopeList())
        assign = ast.Assign(targets=[ast.Name(id=self._has_break_var_name)], value=None)
        # Manually set scopes attribute after construction
        assign.targets[0].scopes = scopes
        ast.fix_missing_locations(assign)
        body = []
        for n in node.body:
            if hasattr(n, "if_expr"):
                assign.value = ast.Constant(value=False)
                assign.value.scopes = scopes
                body.append(assign)
                body.append(n)
                body.append(n.if_expr)
            elif isinstance(n, ast.Break):
                for_node = find_node_by_type((ast.For, ast.While), scopes)
                if hasattr(for_node, "if_expr"):
                    assign.value = ast.Constant(value=True)
                    assign.value.scopes = scopes
                    body.append(assign)
                body.append(n)
            else:
                body.append(n)

        node.body = body


class SelfMutatingMethodRewriter(ast.NodeTransformer):
    """Rewrite methods that mutate ``self`` fields and ``return self`` into the
    equivalent functional form ``return ClassName(...)``.

    Backends like Lean and SMT have no in-place object
    mutation, so ``self.balance += amount; return self`` must become
    ``return BankAccount(self.balance + amount)``.  The Python backend keeps
    the mutation as written.  Field updates are folded in program order, so
    ``self.a += x; self.b = self.a + 1; return self`` becomes
    ``return C(self.a + x, self.a + 1)`` for fields ``(a, b)``.
    """

    def __init__(self, language: str):
        super().__init__()
        # Python keeps in-place mutation; Rust expresses it natively via a
        # ``&mut self`` receiver.  The remaining backends get the functional
        # rewrite.
        self._enable = language in {"lean", "smt"}
        self._class_name = None
        self._class_fields = []

    def visit_ClassDef(self, node):
        if not self._enable:
            return node
        # Field declarations are class-body ``AnnAssign``/``Assign`` to Names
        # (dataclass style); the order matters for the positional constructor.
        fields = []
        for b in node.body:
            if isinstance(b, ast.AnnAssign) and isinstance(b.target, ast.Name):
                fields.append(b.target.id)
            elif (
                isinstance(b, ast.Assign)
                and len(b.targets) == 1
                and isinstance(b.targets[0], ast.Name)
            ):
                fields.append(b.targets[0].id)
        saved_name, saved_fields = self._class_name, self._class_fields
        self._class_name = node.name
        self._class_fields = fields
        self.generic_visit(node)
        self._class_name, self._class_fields = saved_name, saved_fields
        return node

    def visit_FunctionDef(self, node):
        if not self._enable or not self._class_fields:
            return node
        args = node.args.args
        if not args or getattr(args[0], "arg", None) != "self":
            return node

        # Fold ``self.<field> = / += ...`` updates in program order.
        cur = {}
        mutations = []
        returns_self = False
        for stmt in node.body:
            if isinstance(stmt, (ast.Assign, ast.AugAssign)):
                # target is ``targets[0]`` for Assign, ``target`` for AugAssign;
                # never touch ``.target`` on an Assign (it does not exist) and
                # never touch ``.targets`` on an AugAssign (getattr's default is
                # evaluated eagerly, so it must not read ``.target`` either).
                target = (
                    stmt.targets[0] if isinstance(stmt, ast.Assign) else stmt.target
                )
                n_targets = len(stmt.targets) if isinstance(stmt, ast.Assign) else 1
                if n_targets == 1 and isinstance(target, ast.Attribute):
                    if isinstance(target.value, ast.Name) and target.value.id == "self":
                        f = target.attr
                        if f not in self._class_fields:
                            # Unknown field; don't attempt the rewrite.
                            return node
                        left = cur.get(f) or ast.Attribute(
                            value=ast.Name(id="self", ctx=ast.Load()),
                            attr=f,
                            ctx=ast.Load(),
                        )
                        if isinstance(stmt, ast.AugAssign):
                            cur[f] = ast.BinOp(left=left, op=stmt.op, right=stmt.value)
                        else:
                            cur[f] = stmt.value
                        mutations.append(stmt)
            elif (
                isinstance(stmt, ast.Return)
                and isinstance(stmt.value, ast.Name)
                and stmt.value.id == "self"
            ):
                returns_self = True

        if not returns_self or not mutations:
            return node

        # Rebuild the body: drop the field updates, and point ``return self``
        # at a fresh constructor call carrying every field (updated ones folded).
        ctor = ast.Call(
            func=ast.Name(id=self._class_name, ctx=ast.Load()),
            args=[
                cur.get(f)
                or ast.Attribute(
                    value=ast.Name(id="self", ctx=ast.Load()),
                    attr=f,
                    ctx=ast.Load(),
                )
                for f in self._class_fields
            ],
            keywords=[],
        )
        new_body = []
        for stmt in node.body:
            if stmt in mutations:
                continue
            if (
                isinstance(stmt, ast.Return)
                and isinstance(stmt.value, ast.Name)
                and stmt.value.id == "self"
            ):
                stmt.value = ctor
            new_body.append(stmt)
        node.body = new_body
        ast.fix_missing_locations(node)
        return node


class CheckerBlockRemover(ast.NodeTransformer):
    """Strips ``if CHECKER.pre:`` / ``if CHECKER.post:`` / ``if CHECKER.invariant:``
    blocks from the AST for backends that do not process them (all except Lean).

    Verifies that ``CHECKER`` was imported from ``py2many.spec`` before stripping.
    """

    def __init__(self, language: str):
        super().__init__()
        self._language = language
        self._checker_import_verified = False

    def _is_checker_import_from_spec(self, tree: ast.Module) -> bool:
        """Scan module-level imports for ``from py2many.spec import CHECKER``."""
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                if node.module == "py2many.spec":
                    for alias in node.names:
                        if alias.name == "CHECKER":
                            return True
        return False

    def visit_Module(self, node: ast.Module) -> ast.Module:
        if self._language == "lean":
            return node  # Lean handles CHECKER blocks itself
        self._checker_import_verified = self._is_checker_import_from_spec(node)
        self.generic_visit(node)
        return node

    def visit_If(self, node: ast.If) -> Any:
        if not self._checker_import_verified:
            return node
        if isinstance(node.test, ast.Attribute):
            if (
                isinstance(node.test.value, ast.Name)
                and node.test.value.id == "CHECKER"
            ):
                # Strip the entire if block
                return None
        return node
