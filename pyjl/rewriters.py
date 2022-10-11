import ast
from typing import Any

from py2many.ast_helpers import get_id
from py2many.tracer import is_class_or_module
from pyjl.clike import JL_IGNORED_MODULE_SET


class JuliaMethodCallRewriter(ast.NodeTransformer):
    """Converts Python calls and attribute calls to Julia compatible ones"""
    def __init__(self) -> None:
        super().__init__()
        self._file = None
        self._basedir = None
        self._ignored_module_set = JL_IGNORED_MODULE_SET
        self._imports = []
        # self._use_modules = None
        # self._oop_nested_funcs = False

    def visit_Module(self, node: ast.Module) -> Any:
        self._file = getattr(node, "__file__", ".")
        self._basedir = getattr(node, "__basedir__", None)
        # self._use_modules = getattr(node, USE_MODULES, 
        #     FLAG_DEFAULTS[USE_MODULES])
        self._imports = list(map(get_id, getattr(node, "imports", [])))
        # self._oop_nested_funcs = getattr(node, OOP_NESTED_FUNCS, 
        #     FLAG_DEFAULTS[OOP_NESTED_FUNCS]) 
        self.generic_visit(node)
        return node

    def visit_Call(self, node: ast.Call):
        self.generic_visit(node)

        # Special attribute used for dispatching
        node.orig_name = get_id(node.func)
        ann = None
        if id := get_id(node.func):
            module_name = id.split(".")
            module_node = node.scopes.find(module_name[1]) \
                if module_name[0] == "self" \
                else node.scopes.find(module_name[0])
            ann = getattr(module_node, "annotation", None)

        # Don't parse annotations and special nodes
        is_module_call = False
        if isinstance(node.func, ast.Attribute):
            is_module_call = \
                get_id(getattr(node.func.value, "annotation", None)) == "Module"
        if getattr(node, "is_annotation", False) or \
                getattr(node, "no_rewrite", False) or \
                getattr(node.func, "no_rewrite", False) or \
                get_id(ann) == "Module" or \
                is_module_call:
            return node

        args = node.args
        fname = node.func
        if isinstance(fname, ast.Attribute):
            val_id = get_id(fname.value)
            if not is_class_or_module(val_id, node.scopes):
                args = [fname.value] + args
                new_func_name = fname.attr
                node.func = ast.Name(
                    id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        node.args = args
        return node

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        self.generic_visit(node)
        # Don't parse annotations or special nodes
        if getattr(node, "is_annotation", False) or \
                getattr(node, "no_rewrite", False):
            return node
        # Get annotation
        annotation = getattr(node, "annotation", None)
        # Adds a dispatch attribute, as functions can be assigned to variables
        node.dispatch = ast.Call(
            func = ast.Name(id=node.attr, ctx=ast.Load(), lineno = node.lineno),
            args=[node.value],
            keywords=[],
            lineno=node.lineno,
            col_offset=node.col_offset,
            annotation = annotation,
            scopes = node.scopes,
            is_attr = True,
            orig_name = get_id(node), # Special attribute used for dispatching
            in_ccall = getattr(node, "in_ccall", None), # Propagate ccall information
        )
        return node

class JuliaIndexingRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        call_id = get_id(node.func)
        if call_id == "range" or call_id == "xrange":
            # decrement stop
            if len(node.args) == 1:
                node.args[0] = self._do_bin_op(
                    node.args[0], ast.Sub(), 1, node.lineno, node.col_offset
                )
            elif len(node.args) > 1:
                node.args[1] = self._do_bin_op(
                    node.args[1], ast.Sub(), 1, node.lineno, node.col_offset
                )
            if len(node.args) == 3:
                # Cover reverse lookup
                if isinstance(node.args[2], ast.UnaryOp) and isinstance(
                    node.args[2].op, ast.USub
                ):
                    node.args[0], node.args[1] = node.args[1], node.args[0]
        return node

    def _do_bin_op(self, node, op, val, lineno, col_offset):
        left = node
        left.annotation = ast.Name(id="int")
        return ast.BinOp(
            left=left,
            op=op,
            right=ast.Constant(
                value=val, annotation=ast.Name(id="int"), scopes=node.scopes
            ),
            lineno=lineno,
            col_offset=col_offset,
            scopes=node.scopes,
        )
