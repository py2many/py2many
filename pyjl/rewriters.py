from __future__ import annotations
import ast
from typing import Any, Dict

from py2many.exceptions import AstUnsupportedOperation
from py2many.tracer import find_in_scope, is_class_or_module, is_enum
from py2many.analysis import IGNORED_MODULE_SET

from py2many.input_configuration import ParseFileStructure
from py2many.tracer import find_node_by_type
from py2many.ast_helpers import get_id
from pyjl.clike import JL_IGNORED_MODULE_SET
from pyjl.helpers import find_assign_value, get_str_repr, get_variable_name
import pyjl.juliaAst as juliaAst
from pyjl.plugins import JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE


def julia_config_rewriter(tree, input_config, filename):
    JuliaConfigRewriter(input_config, filename).visit(tree)


class JuliaMethodCallRewriter(ast.NodeTransformer):

    def visit_Call(self, node):
        args = []
        if node.args:
            args += [self.visit(a) for a in node.args]

        fname = node.func
        if isinstance(fname, ast.Attribute):
            new_func_name = fname.attr

            if get_id(fname.value):
                node0 = ast.Name(id=get_id(fname.value), lineno=node.lineno)
            else:
                node0 = fname.value

            args = [node0] + node.args

            node.func = ast.Name(
                id=new_func_name, lineno=node.lineno, ctx=fname.ctx)

        node.args = args
        return self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        value_id = None
        if node_id := get_id(node.value):
            value_id = node_id
        elif isinstance(node.value, ast.Call)\
                and (call_id := get_id(node.value.func)):
            value_id = call_id

        if value_id and (is_enum(value_id, node.scopes) or
                         is_class_or_module(value_id, node.scopes) or
                         value_id.startswith("self")):
            return node

        return ast.Call(
            func=ast.Name(id=node.attr, ctx=ast.Load()),
            args=[node.value],
            keywords=[],
            lineno=node.lineno,
            col_offset=node.col_offset)


class JuliaConfigRewriter(ast.NodeTransformer):
    def __init__(self, input_config: Dict, filename: str) -> None:
        super().__init__()
        self._input_config_map = (ParseFileStructure.retrieve_structure(filename, input_config)
                                  if input_config else None)

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)
        node_name = get_id(node)
        node_scope_name = None
        if self._input_config_map:
            if len(node.scopes) > 2:
                node_class = find_node_by_type(ast.ClassDef, node.scopes)
                node_scope_name = get_id(node_class) if node_class else None

            node_field_map = ParseFileStructure.get_function_attributes(node_name,
                                                                        node_scope_name, self._input_config_map)

            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        class_name = get_id(node)
        if self._input_config_map:
            node_field_map = ParseFileStructure.get_class_attributes(
                class_name, self._input_config_map)
            if "decorators" in node_field_map:
                node.decorator_list += node_field_map["decorators"]
                # Remove duplicates
                node.decorator_list = list(set(node.decorator_list))
                # Transform in Name nodes
                node.decorator_list = list(
                    map(lambda dec: ast.Name(id=dec), node.decorator_list))

        return node


class JuliaClassRewriter(ast.NodeTransformer):
    """Transforms Python classes into Julia compatible classes"""

    def __init__(self) -> None:
        super().__init__()
        self._hierarchy_map = {}
        self._import_list = []
        self._import_count = 0
        self._ignored_module_set = \
            self._ignored_module_set = IGNORED_MODULE_SET.copy()\
                .union(JL_IGNORED_MODULE_SET.copy())
        self._class_fields: Dict[str, Any] = {}
        self._nested_classes = []

    def visit_Module(self, node: ast.Module) -> Any:
        self._hierarchy_map = {}
        self._import_list = []
        self._import_count = 0
        self._nested_classes = []

        node.lineno = 0
        node.col_offset = 0

        # Visit body nodes
        body = []
        for n in node.body:
            self._class_fields = {}
            if isinstance(n, ast.ClassDef):
                class_body = []
                for d in n.body:
                    if isinstance(d, ast.FunctionDef):
                        if d.name in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
                            JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE[d.name](
                                self, d)
                        else:
                            d.self_type = n.name
                            class_body.append(self.visit(d))
                    else:
                        class_body.append(self.visit(d))
                fields = []
                for f in self._class_fields.values():
                    if f is not None:
                        fields.append(f)
                n.body = fields + class_body

            b_node = self.visit(n)

            if self._nested_classes:                    
                for cls in self._nested_classes:
                    body.append(self.visit(cls))
                self._nested_classes = []

            body.append(b_node)

        # Create abstract types
        abstract_types = []
        l_no = self._import_count
        for (class_name, (extends_lst, is_jlClass)) in self._hierarchy_map.items():
            # node.class_names.append(class_name)
            if not is_jlClass:
                core_module = extends_lst[0].split(
                    ".")[0] if extends_lst else None
                # TODO: Investigate Julia traits
                nameVal = ast.Name(id=class_name)
                extends = ast.Name(id=f"Abstract{extends_lst[0]}") \
                    if extends_lst and core_module not in self._ignored_module_set \
                    else None
                abstract_types.append(
                    juliaAst.AbstractType(value=nameVal, extends=extends,
                                          ctx=ast.Load(), lineno=l_no, col_offset=0))
                # increment linenumber
                l_no += 1

        if abstract_types:
            body = body[:self._import_count] + \
                abstract_types + body[self._import_count:]

        node.body = body

        return node

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        class_name: str = get_id(node)

        decorator_list = list(map(get_id, node.decorator_list))
        is_jlClass = "jl_class" in decorator_list

        extends = []
        if not node.bases or len(node.bases) == 0:
            node.jl_bases = [
                ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]
        elif len(node.bases) == 1:
            name = get_id(node.bases[0])
            node.jl_bases = [
                ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)]
            extends = [name]
        elif len(node.bases) > 1:
            # TODO: Investigate Julia traits
            new_bases = []
            for base in node.bases:
                name = get_id(base)
                if is_class_or_module(name, node.scopes) or name in self._import_list:
                    b = ast.Name(id=f"Abstract{class_name}", ctx=ast.Load)
                    if b not in new_bases:
                        new_bases.append(b)
                else:
                    new_bases.append(base)
                extends.append(name)
            node.jl_bases = new_bases

        self._hierarchy_map[class_name] = (extends, is_jlClass)

        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        args = node.args

        for arg in args.args:
            if ((annotation := getattr(arg, "annotation", None)) and
                    is_class_or_module(annotation, node.scopes)):
                setattr(annotation, "id", f"Abstract{annotation}")

        if (hasattr(node, "self_type") and
                is_class_or_module(node.self_type, node.scopes)):
            node.self_type = f"Abstract{node.self_type}"

        # Remove any classes from function body 
        # if @remove_nested decorator is present
        body = []
        for n in node.body:
            if isinstance(n, ast.ClassDef) and \
                    "remove_nested" in map(get_str_repr, n.decorator_list):
                self._nested_classes.append(n)
            else:
                body.append(self.visit(n))

        node.body = body

        return self.generic_visit(node)

    # TODO: Rewrite special method calls
    # def visit_Call(self, node: ast.Call) -> Any:
    #     fname = node.func
    #     if fname in JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE:
    #         pass
    #     return node

    def visit_Expr(self, node: ast.Expr) -> Any:
        parent = node.scopes[-1]
        # Initialize class expression with None type
        if isinstance(parent, ast.ClassDef) and (id := get_id(node.value)):
            self._class_fields[id] = None
        return self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> Any:
        target = node.targets[0]
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        target = node.target
        self._generic_assign_visit(node, target)
        return self.generic_visit(node)

    def _generic_assign_visit(self, node, target):
        if self._is_member(target):
            if target.attr not in self._class_fields:
                self._class_fields[target.attr] = node
            else:
                class_field = self._class_fields[target.attr]
                if class_field.value is None and node.value:
                    self._class_fields[target.attr] = node

    def _is_member(self, node):
        return hasattr(node, "value") and get_id(node.value) == "self"

    def visit_Import(self, node: ast.Import) -> Any:
        self._generic_import_visit(node)
        return self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> Any:
        self._generic_import_visit(node)
        return self.generic_visit(node)

    def _generic_import_visit(self, node):
        is_visit = False
        for alias in node.names:
            alias_id = alias.name
            if alias_id not in self._ignored_module_set:
                is_visit = True
                if asname := getattr(alias, "asname", None):
                    self._import_list.append(asname)
                elif name := getattr(alias, "name", None):
                    self._import_list.append(name)

        if is_visit:
            self._import_count += 1


class JuliaAugAssignRewriter(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        requires_lowering = (
            isinstance(node.op, ast.BitXor) or
            isinstance(node.op, ast.BitAnd) or
            ((isinstance(node.op, ast.Add) or
              isinstance(node.op, ast.Mult) or
              isinstance(node.op, ast.MatMult)) and
                (self._is_list(node.target, node.scopes) or
                 self._is_list(node.value, node.scopes)))
        )
        if requires_lowering:
            return ast.Assign(
                targets=[node.target],
                value=ast.BinOp(
                    left=node.target,
                    op=node.op,
                    right=node.value,
                    lineno=node.lineno,
                    col_offset=node.col_offset
                ),
                lineno=node.lineno,
                col_offset=node.col_offset
            )

        return self.generic_visit(node)

    def _is_list(self, node, scopes):
        if isinstance(node, ast.List):
            return True
        if (isinstance(node, ast.Subscript) and (id := get_id(node.value))) or (id := get_id(node)):
            val = find_assign_value(id, node.scopes)
            return isinstance(val, ast.List) or isinstance(val, ast.List)
        return False

# TODO: Not actually a Rewriter (more of a transformer)
class JuliaDecoratorRewriter(ast.NodeTransformer):
    def __init__(self):
        super().__init__()

    def visit_ClassDef(self, node: ast.ClassDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        self._parse_decorators(node)
        return self.generic_visit(node)

    def _parse_decorators(self, node):
        parsed_decorators: Dict[str, Dict[str, str]] = {}
        if decorator_list := getattr(node, "decorator_list", None):
            for decorator in decorator_list:
                if isinstance(decorator, ast.Name):
                    parsed_decorators[get_id(decorator)] = None
                elif isinstance(decorator, ast.Call):
                    keywords = {}
                    for keyword in decorator.keywords:
                        keywords[keyword.arg] = keyword.value.value
                    parsed_decorators[get_id(decorator.func)] = keywords
                
        if "dataclass" in parsed_decorators \
                and "jl_dataclass" in parsed_decorators:
            parsed_decorators.pop("dataclass")

        node.parsed_decorators = parsed_decorators

class JuliaGeneratorRewriter(ast.NodeTransformer):
    def __init__(self):
        self._generator_funcs = {}
        self._assign_map = {}
        self._nested_funcs = []
        super().__init__()

    def visit_Module(self, node: ast.Module) -> Any:
        body = []
        for n in node.body:
            b_node = self.visit(n)
            if isinstance(n, ast.FunctionDef):
                if self._nested_funcs:
                    for nested in self._nested_funcs:
                        body.append(self.visit(nested))
                    self._nested_funcs = []

            body.append(b_node)

        node.body = body

        return node

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Any:
        yield_node = find_in_scope(
            node.body, lambda x: isinstance(x, ast.Yield))

        body = []
        for n in node.body:
            if isinstance(n, ast.FunctionDef) and "resumable" in n.parsed_decorators:
                resumable = n.parsed_decorators["resumable"]
                if "remove_nested" in resumable \
                        and resumable["remove_nested"]:
                    self._nested_funcs.append(n)
                    continue
            body.append(self.visit(n))
        node.body = body

        if "resumable" in node.parsed_decorators and \
                "channels" in node.parsed_decorators:
            raise AstUnsupportedOperation(  
                "Function cannot have both @resumable and @channels decorators", 
                node)

        is_resumable = "resumable" in node.parsed_decorators \
            or ("resumable" in node.parsed_decorators and 
                node.parsed_decorators["resumable"])
        self._generator_funcs[node.name] = is_resumable
        if yield_node and not is_resumable:
            # Body contains yield and is not resumable function
            node.body = [
                ast.With(
                    items = [
                        ast.withitem(
                            context_expr = ast.Call(
                                func=ast.Name(
                                    id = "Channel",
                                    lineno = node.lineno,
                                    col_offset = node.col_offset),
                                args = [],
                                keywords = [],
                                scopes = [],
                                lineno = node.lineno,
                                col_offset = node.col_offset),
                            optional_vars = ast.Name(
                                id = f"ch_{node.name}",
                                lineno = node.lineno,
                                col_offset = node.col_offset)
                        )
                    ],
                    body = node.body,
                    lineno = node.lineno,
                    col_offset = node.col_offset)
            ]

        return self.generic_visit(node)

    def visit_YieldFrom(self, node: ast.YieldFrom) -> Any:
        parent = node.scopes[-1]
        if isinstance(parent, ast.FunctionDef):
            dec = None
            if "channels" in parent.parsed_decorators:
                dec = parent.parsed_decorators["channels"]
            elif "resumable" in parent.parsed_decorators:
                dec = parent.parsed_decorators["resumable"]
            lower_yield_from = dec and dec["lower_yield_from"]
            if lower_yield_from:
                val = ast.Name(
                        id = get_variable_name(parent),
                        lineno = node.lineno,
                        col_offset = node.col_offset)
                new_node = ast.For(
                    target = val,
                    iter = node.value,
                    body = [
                        ast.Yield(
                            value = val
                        )],
                    lineno = node.lineno,
                    col_offset = node.col_offset)
                return new_node

        return self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> Any:
        if isinstance(node.value, ast.List) or isinstance(node.value, ast.Tuple):
            value_list = map(lambda x: get_str_repr(x) if isinstance(x, ast.Call) else None, node.value.elts)
            for target, value in zip(node.targets, value_list):
                if value and (t_id := get_id(target)):
                    self._assign_map[t_id] = get_str_repr(node.value)
        else:
            if isinstance(node.value, ast.Call):
                for target in node.targets:
                    if t_id := get_id(target):
                        self._assign_map[t_id] = get_str_repr(node.value)

        return self.generic_visit(node)
    
    # TODO: Both visit_Attribute and visit_Call are a fallback. 
    # If inference can detect Generator functions, add this to the dispatch_map 
    def visit_Attribute(self, node: ast.Attribute) -> Any:
        if id := get_id(node.value):
            if id in self._assign_map:
                assign_res = self._assign_map[id]
                if assign_res in self._generator_funcs:
                    if node.attr == "__next__":
                        node.attr = (f"{assign_res}()"
                            if self._generator_funcs[assign_res]
                            else "take!")
        return self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> Any:
        if (id := get_id(node.func)) and len(node.args) > 0:
            arg = get_id(node.args[0])
            if arg in self._assign_map:
                assign_res = self._assign_map[arg]
                if assign_res in self._generator_funcs:
                    if id == "next":
                        if self._generator_funcs[assign_res]:
                            new_id = f"{arg}"
                            node.args = node.args[1:]
                        else:
                            new_id = "take!"
                        node.func = ast.Name(
                            id = new_id,
                            lineno = node.lineno,
                            col_offset = node.col_offset)
        return self.generic_visit(node)

# Is this useful?
# class JuliaTypeRewriter(ast.NodeTransformer):
#     def __init__(self) -> None:
#         super().__init__()

#     def visit_BinOp(self, node: ast.BinOp) -> Any:
#         left_jl_ann: str = getattr(node.left, "julia_annotation", "nothing")
#         right_jl_ann: str = getattr(node.right, "julia_annotation", "nothing")

#         build_list = lambda x: ast.List(
#                         elts = x.elts,
#                         lineno = x.lineno,
#                         col_offset = x.col_offset,
#                         julia_annotation = 
#                             x.julia_annotation.replace("Tuple", "Vector", 1))

#         if isinstance(node.op, ast.Mult):
#             if (isinstance(node.right, ast.Num) or (right_jl_ann.startswith("Int"))) and \
#                     isinstance(node.left, ast.Tuple):
#                 node.left = build_list(node.left)

#             if (isinstance(node.left, ast.Num) or (left_jl_ann.startswith("Int"))) and \
#                     isinstance(node.right, ast.Tuple):
#                 node.right = build_list(node.right)

#         return self.generic_visit(node)