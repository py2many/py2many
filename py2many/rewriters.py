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
        if self._language in {"mojo", "python"}:
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
        if isinstance(node, ast.Str):
            return node
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
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
        self._disable = language in {"nim", "v"}
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
                    comparators=[ast.Constant(value=True, scopes=scopes)],
                    scopes=scopes,
                ),
                body=[oe for oe in node.orelse],
                orelse=[],
                lineno=lineno,
                scopes=scopes,
            )
            node.if_expr = if_expr

    def _visit_Scope(self, node) -> Any:
        self.generic_visit(node)
        scopes = getattr(node, "scopes", ScopeList())
        assign = ast.Assign(
            targets=[ast.Name(id=self._has_break_var_name)], value=None, scopes=scopes
        )
        ast.fix_missing_locations(assign)
        body = []
        for n in node.body:
            if hasattr(n, "if_expr"):
                assign.value = ast.Constant(value=False, scopes=scopes)
                body.append(assign)
                body.append(n)
                body.append(n.if_expr)
            elif isinstance(n, ast.Break):
                for_node = find_node_by_type((ast.For, ast.While), scopes)
                if hasattr(for_node, "if_expr"):
                    assign.value = ast.Constant(value=True, scopes=scopes)
                    body.append(assign)
                body.append(n)
            else:
                body.append(n)

        node.body = body
