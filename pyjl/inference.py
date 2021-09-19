import ast

from py2many.exceptions import AstUnrecognisedBinOp
from py2many.analysis import get_id

class InferJuliaTypesTransformer(ast.NodeTransformer):

    def visit_BinOp(self, node):
        self.generic_visit(node)

        if isinstance(node.left, ast.Name):
            lvar = node.scopes.find(get_id(node.left))
        else:
            lvar = node.left

        if isinstance(node.right, ast.Name):
            rvar = node.scopes.find(get_id(node.right))
        else:
            rvar = node.right

        left = lvar.annotation if lvar and hasattr(lvar, "annotation") else None
        right = rvar.annotation if rvar and hasattr(rvar, "annotation") else None

        if left is None and right is not None:
            node.annotation = right # TODO: See if types need translation
            return node

        if right is None and left is not None:
            node.annotation = left # TODO: See if types need translation
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        if left_id == right_id and left_id == "int":
            if not isinstance(node.op, ast.Div) or getattr(
                node, "use_integer_div", False
            ):
                node.annotation = left
            else:
                node.annotation = ast.Name(id="float")
            return node

        if left_id == "int":
            left_id = "c_int32"
        if right_id == "int":
            right_id = "c_int32"

        if (
            left_id in self.FIXED_WIDTH_INTS_NAME
            and right_id in self.FIXED_WIDTH_INTS_NAME
        ):
            ret = self._handle_overflow(node.op, left_id, right_id)
            node.annotation = ast.Name(id=ret)
            return node
        if left_id == right_id: # Check this. In rust it was removed
            # Exceptions: division operator
            if isinstance(node.op, ast.Div):
                if left_id == "int":
                    node.annotation = ast.Name(id="float")
                    return node
            node.annotation = left
            return node

        if left_id in self.FIXED_WIDTH_INTS_NAME:
            left_id = "int"
        if right_id in self.FIXED_WIDTH_INTS_NAME:
            right_id = "int"
        if (left_id, right_id) in {("int", "float"), ("float", "int")}:
            node.annotation = ast.Name(id="float")
            return node
        if (left_id, right_id) in {
            ("int", "complex"),
            ("complex", "int"),
            ("float", "complex"),
            ("complex", "float"),
        }:
            node.annotation = ast.Name(id="complex")
            return node

        # Container multiplication
        if isinstance(node.op, ast.Mult) and {left_id, right_id} in [
            {"bytes", "int"},
            {"str", "int"},
            {"tuple", "int"},
            {"List", "int"},
        ]:
            node.annotation = ast.Name(id=left_id)
            return node

        LEGAL_COMBINATIONS = {("str", ast.Mod), ("List", ast.Add), ("int", ast.Add)}

        # if left_id is not None and (left_id, type(node.op)) not in LEGAL_COMBINATIONS:
        #     raise AstUnrecognisedBinOp(left_id, right_id, node)

        return node

