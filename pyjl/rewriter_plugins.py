import ast
from py2many.scope import ScopeList
import pyjl.juliaAst as juliaAst

from py2many.ast_helpers import get_id
from py2many.declaration_extractor import DeclarationExtractor
from py2many.tracer import find_node_by_type, is_class_or_module
from pyjl.transpiler import JuliaTranspiler


class SpecialFunctionsPlugins():
    def visit_init(self, node: ast.FunctionDef):
        # Remove self
        node.args.args = node.args.args[1:]
        is_oop = getattr(node, "oop", False)
        constructor_calls = []
        constructor_body = []
        is_self = lambda x: isinstance(x, ast.Attribute) and \
            get_id(x.value) == "self"
        for n in node.body:
            if isinstance(n, ast.Assign) and is_self(n.targets[0]) or \
                    isinstance(n, ast.AnnAssign) and is_self(n.target):
                continue
            elif is_oop and isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) \
                    and is_class_or_module(get_id(n.value.func), node.scopes):
                constructor_calls.append(n)
            else:
                constructor_body.append(n)

        
        constructor = None
        class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
        if is_oop:
            assignments = [ast.Assign(
                    targets = [ast.Name(id=declaration)],
                    value = ast.Name(id=declaration))
                for declaration in class_node.declarations.keys()]
            body = constructor_calls + assignments
            make_block = juliaAst.Block(
                            name = "@mk",
                            body = body)
            ast.fix_missing_locations(make_block)
            constructor_body.append(make_block)
            constructor = ast.FunctionDef(
                name = "new",
                args = node.args,
                body = constructor_body,
            )
        else:
            struct_name = get_id(class_node)
            has_default = node.args.defaults != []
            if constructor_body or has_default:
                decls = list(map(lambda x: ast.Name(id=x.arg), node.args.args))
                decorator_list = list(map(get_id, class_node.decorator_list))
                if "jl_class" not in decorator_list:
                    # If we are using composition and the class extends from super, 
                    # it must contain its fields as well.
                    # We assume that all the fields provided in the __init__ function 
                    # as args are the ones required.
                    for decl in decls:
                        decl_id = get_id(decl)
                        if decl_id not in class_node.declarations:
                            class_node.declarations[decl_id] = None
                            class_node.declarations_with_defaults[decl_id] = (None, None)
                # decls = list(map(lambda x: ast.Name(id=x), class_node.declarations.keys()))
                new_instance = ast.Call(
                                func = ast.Name(id = "new"),
                                args = decls,
                                keywords = [],
                                scopes = ScopeList())
                ast.fix_missing_locations(new_instance)
                constructor_body.append(new_instance)
                constructor = juliaAst.Constructor(
                    name = struct_name,
                    args = node.args,
                    body = constructor_body,
                )

        if constructor:
            ast.fix_missing_locations(constructor)
            constructor.scopes = ScopeList(),
            constructor.parsed_decorators = node.parsed_decorators
            constructor.decorator_list = node.decorator_list
            class_node.constructor = constructor
        
        # Used to order the struct fields
        class_node.constructor_args = node.args

        return None

# Dispatches special Functions
JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE = {
    "__init__": SpecialFunctionsPlugins.visit_init,
}
