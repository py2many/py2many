import ast
import textwrap

from py2many.analysis import get_id

from typing import Optional


class ComplexDestructuringRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._disable = False
        if language in {"cpp", "julia", "dart"}:
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
            ret = ast.If(
                test=ast.Constant(value=True), body=body, orelse=[], lineno=node.lineno
            )
            return ret
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


def capitalize_first(name):
    first = name[0].upper()
    return first + name[1:]


def camel_case(name):
    if "_" not in name:
        return name
    return "".join(capitalize_first(part) for part in name.split("_"))


def rename(scope, old_name, new_name):
    tx = RenameTransformer(old_name, new_name)
    tx.visit(scope)


class PythonMainRewriter(ast.NodeTransformer):
    def __init__(self, language):
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
            ret = ast.parse("def main(): True").body[0]
            ret.lineno = node.lineno
            ret.body = node.body
            # So backends know to insert argc, argv etc
            ret.python_main = True
            return ret
        return node


class FStringJoinRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()

    def visit_JoinedStr(self, node):
        new_node = ast.parse('"".join([])').body[0].value
        args = new_node.args
        for v in node.values:
            if isinstance(v, ast.Constant):
                args[0].elts.append(v)
            elif isinstance(v, ast.FormattedValue):
                args[0].elts.append(
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

    def visit_FunctionDef(self, node):
        doc_node = self._get_doc_node(node)
        self._docstrings.add(doc_node)
        self._docstring_parent[doc_node] = node
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node):
        doc_node = self._get_doc_node(node)
        self._docstrings.add(doc_node)
        self._docstring_parent[doc_node] = node
        self.generic_visit(node)
        return node

    def visit_Module(self, node):
        doc_node = self._get_doc_node(node)
        self._docstrings.add(doc_node)
        self._docstring_parent[doc_node] = node
        self.generic_visit(node)
        return node

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
        ifexpr = ast.parse("'True' if true else 'False'").body[0].value
        ifexpr.test = node.args[0]
        ifexpr.lineno = node.lineno
        ifexpr.col_offset = node.col_offset
        ast.fix_missing_locations(ifexpr)
        node.args[0] = ifexpr
        return node

    # Go can't handle IfExpr in print. Handle it differently here
    def _do_go_rewrite(self, node) -> ast.AST:
        if_stmt = ast.parse(
            textwrap.dedent(
                """\
            if True:
                print('True')
            else:
                print('False')
        """
            )
        ).body[0]
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
