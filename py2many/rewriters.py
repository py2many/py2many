import ast


class ComplexDestructuringRewriter(ast.NodeTransformer):
    def __init__(self, language):
        super().__init__()
        self._disable = False
        if language in {"cpp", "julia"}:
            self._disable = True
        self._temp = 0

    def _get_temp(self):
        self._temp += 1
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
            # ast.parse produces a Module object that needs to be destructured
            ret = ast.parse("def main(): True").body[0]
            ret.lineno = node.lineno
            ret.body = node.body
            # So backends know to insert argc, argv etc
            ret.python_main = True
            return ret
        return node
