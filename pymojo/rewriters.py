import ast

from py2many.analysis import get_id
from py2many.ast_helpers import create_ast_node


class MojoImplicitConstructor(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node):
        needs_init = "dataclass" not in [get_id(n) for n in node.decorator_list]
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                if b.name == "__init__":
                    needs_init = False

        if not needs_init:
            return node

        new_node = create_ast_node("def __init__(self): pass")
        ast.fix_missing_locations(new_node)
        node.body.insert(0, new_node)
        return node


class MojoDictKeysInElider(ast.NodeTransformer):
    """Rewrite `x in d.keys()` to `x in d`.

    Mojo's `Dict.keys()` returns `_DictKeyIter`, which doesn't implement
    `__contains__`. In Python both forms are equivalent for dicts, so dropping
    the `.keys()` call is semantics-preserving and lets the emission go through
    Mojo's `Dict.__contains__`.
    """

    def visit_Compare(self, node):
        self.generic_visit(node)
        if (
            len(node.ops) == 1
            and isinstance(node.ops[0], ast.In)
            and len(node.comparators) == 1
        ):
            rhs = node.comparators[0]
            if (
                isinstance(rhs, ast.Call)
                and isinstance(rhs.func, ast.Attribute)
                and rhs.func.attr == "keys"
                and not rhs.args
                and not rhs.keywords
            ):
                node.comparators = [rhs.func.value]
        return node


class MojoInferMoveSemantics(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_arg(self, node):
        node.is_arg = True
        return node

    def visit_Return(self, node):
        if node.value:
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                definition = node.scopes.find(get_id(node.value))
                if definition is None:
                    for arg in fndef.args.args:
                        if get_id(node.value) == get_id(arg):
                            definition = arg
                            break
                if definition and getattr(definition, "is_arg", None):
                    node.transfer = True
                    definition.owned = True
        return node
