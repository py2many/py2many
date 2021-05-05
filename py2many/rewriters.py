import ast


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
