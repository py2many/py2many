import ast
import re
from typing import Any

from py2many.ast_helpers import get_id
from py2many.helpers import get_ann_repr

from .pyjl_vars import SEP


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


class JuliaBoolOpRewriter(ast.NodeTransformer):
    """Rewrites condition checks to Julia compatible ones
    All checks that perform equality checks with the literal '1'
    have to be converted to equality checks with true"""

    def __init__(self) -> None:
        super().__init__()

    def visit_If(self, node: ast.If) -> Any:
        self.generic_visit(node)
        self._generic_test_visit(node)
        return node

    def visit_While(self, node: ast.While) -> Any:
        self.generic_visit(node)
        self._generic_test_visit(node)
        return node

    def _generic_test_visit(self, node):
        # Shortcut if conditions are numbers
        if isinstance(node.test, ast.Constant):
            if node.test.value == 1 or node.test.value == "1":
                node.test.value = True
                return node
            elif node.test.value == 0:
                node.test.value = False
                return node

        annotation = getattr(node.test, "annotation", None)
        ann_id = get_ann_repr(annotation, sep=SEP)
        if not isinstance(node.test, ast.Compare) and not isinstance(
            node.test, ast.UnaryOp
        ):
            if ann_id:
                if ann_id != "bool":
                    if ann_id == "int" or ann_id == "float":
                        node.test = self._build_compare(
                            node.test, [ast.NotEq()], [ast.Constant(value=0)]
                        )
                    elif re.match(r"^list|^List", ann_id):
                        # Compare with empty list
                        node.test = self._build_compare(
                            node.test, [ast.IsNot()], [ast.List(elts=[])]
                        )
                    elif re.match(r"^tuple|^Tuple", ann_id):
                        # Compare with empty tuple
                        node.test = self._build_compare(
                            node.test, [ast.IsNot()], [ast.Tuple(elts=[])]
                        )
                    elif re.match(r"^set|^Set", ann_id):
                        # Compare with empty tuple
                        node.test = self._build_compare(
                            node.test, [ast.IsNot()], [ast.Set(elts=[])]
                        )
                    elif re.match(r"^Optional", ann_id):
                        # Compare with type None
                        node.test = self._build_compare(
                            node.test, [ast.IsNot()], [ast.Constant(value=None)]
                        )
                    else:
                        node.test = self._build_runtime_comparison(node)
            else:
                node.test = self._build_runtime_comparison(node)

    def _build_compare(self, node, ops, comp_values):
        for comp_value in comp_values:
            ast.fix_missing_locations(comp_value)
            comp_value.scopes = node.scopes
        return ast.Compare(
            left=node,
            ops=ops,
            comparators=comp_values,
            lineno=node.lineno,
            col_offset=node.col_offset,
            scopes=node.scopes,
        )

    def _build_runtime_comparison(self, node):
        # Perform dynamic comparison
        instance_check = lambda args: ast.Call(
            func=ast.Name(id="isinstance"),
            args=args,
            keywords=[],
            scopes=getattr(node, "scopes", None),
        )
        test_node = ast.BoolOp(
            op=ast.Or(),
            values=[
                ast.BoolOp(
                    op=ast.And(),
                    values=[
                        instance_check(
                            [
                                node.test,
                                ast.Tuple(
                                    elts=[ast.Name(id="int"), ast.Name(id="float")]
                                ),
                            ]
                        ),
                        self._build_compare(
                            node.test, [ast.NotEq()], [ast.Constant(value=0)]
                        ),
                    ],
                ),
                ast.BoolOp(
                    op=ast.And(),
                    values=[
                        instance_check([node.test, ast.Name(id="tuple")]),
                        self._build_compare(
                            node.test, [ast.NotEq()], [ast.Tuple(elts=[])]
                        ),
                    ],
                ),
                ast.BoolOp(
                    op=ast.And(),
                    values=[
                        instance_check([node.test, ast.Name(id="list")]),
                        self._build_compare(
                            node.test, [ast.NotEq()], [ast.List(elts=[])]
                        ),
                    ],
                ),
                ast.BoolOp(
                    op=ast.And(),
                    values=[
                        self._build_compare(
                            node.test, [ast.Is()], [ast.Constant(value=None)]
                        )
                    ],
                ),
                ast.BoolOp(
                    op=ast.And(),
                    values=[
                        instance_check([node.test, ast.Name(id="bool")]),
                        node.test,
                    ],
                ),
            ],
        )
        ast.fix_missing_locations(node.test)
        return test_node

    def visit_Compare(self, node: ast.Compare) -> Any:
        # Julia comparisons with 'None' use Henry Baker's EGAL predicate
        # https://stackoverflow.com/questions/38601141/what-is-the-difference-between-and-comparison-operators-in-julia
        self.generic_visit(node)
        find_none = lambda x: isinstance(x, ast.Constant) and x.value == None
        comps_none = next(filter(find_none, node.comparators), None)
        if find_none(node.left) or comps_none:
            for i in range(len(node.ops)):
                if isinstance(node.ops[i], ast.Eq):
                    node.ops[i] = ast.Is()
                elif isinstance(node.ops[i], ast.NotEq):
                    node.ops[i] = ast.IsNot()
        return node
