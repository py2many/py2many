import ast


def add_annotation_flags(node):
    return AnnotationTransformer().visit(node)


class AnnotationTransformer(ast.NodeTransformer):
    """
    Adds a flag for every type annotation and nested types so they can be differentiated from array
    """

    def __init__(self):
        self.handling_annotation = False

    def visit_arg(self, node):
        if node.annotation:
            self.handling_annotation = True
            self.visit(node.annotation)
            self.handling_annotation = False
        return node

    def visit_FunctionDef(self, node):
        if node.returns:
            self.handling_annotation = True
            self.visit(node.returns)
            self.handling_annotation = False
        self.generic_visit(node)
        return node

    # without this Dict[x,y] will be translated to HashMap<(x,y)>
    def visit_Tuple(self, node):
        if self.handling_annotation:
            node.is_annotation = True
        self.generic_visit(node)
        return node

    def visit_List(self, node):
        if self.handling_annotation:
            node.is_annotation = True
        self.generic_visit(node)
        return node

    def visit_Name(self, node):
        if self.handling_annotation:
            node.is_annotation = True
        self.generic_visit(node)
        return node

    def visit_Subscript(self, node):
        if self.handling_annotation:
            node.is_annotation = True
        self.generic_visit(node)
        return node

    def visit_AnnAssign(self, node):
        self.handling_annotation = True
        self.visit(node.target)
        self.handling_annotation = False
        self.generic_visit(node)
        return node
