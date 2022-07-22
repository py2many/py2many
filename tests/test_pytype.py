import ast
from textwrap import indent
from pytype.tools.annotate_ast import annotate_ast
from pytype.tools.merge_pyi import merge_pyi
import typed_ast.ast3 as tast
import pytype.tools.merge_pyi as merge_pyi
from pytype import analyze, errors, config, load_pytd

def test_tast_annotate():
    code = '''def mult_float_and_int():
    a = 2.0
    return a * 2'''
    tree = tast.parse(code)
    tree.AST = ast.Module
    visitor = annotate_ast.AnnotateAstVisitor(code, tree)
    visitor.visit(tree)
    visitor._maybe_annotate(tree)
    print(tast.dump(tree))

def test_ast_annotate():
    code = '''def mult_float_and_int():
    a = 2.0
    return a * 2'''
    tree = ast.parse(code)
    tree.AST = ast.Module
    tree.Module = ast.Module
    tree.Module.iter_fields = dummy
    tree.ClassDef = ast.ClassDef
    tree.FunctionDef = ast.FunctionDef
    tree.Assign = ast.Assign
    print(annotate_ast.infer_types(code, config.Options.create()).text)
    # visitor = annotate_ast.AnnotateAstVisitor(code, tree)
    # visitor.visit(tree)
    # print(ast.unparse(tree))
    # print(ast.dump(tree, indent=4))

def dummy(node):
    return node

def test_annotate_and_merge():
    code_1 = '''def mult_int_and_string():
    a = 2
    return a * "test"'''
    typed_ast_1, _ = analyze.infer_types(code_1, errors.ErrorLog(), 
        config.Options.create(), load_pytd.Loader(config.Options.create()))
    # Example: getting return type of function
    # We could parse this data into a dictionary and go from there
    print(typed_ast_1.functions[0].signatures[0].return_type)
    ##################
    print("------------")
    code_2 = '''class Foo:
    def bar(self):
        return self.baz()'''
    typed_ast_2, _ = analyze.infer_types(code_2, errors.ErrorLog(), 
        config.Options.create(), load_pytd.Loader(config.Options.create()))
    print(typed_ast_2)
    ##################
    # We may not even need to merge the files
    ann = '''def mult_string_and_int(): str...'''
    # merge_pyi.annotate_string([], code, ann)

if __name__ == "__main__":
    # test_tast_annotate()
    # test_ast_annotate()
    test_annotate_and_merge()

