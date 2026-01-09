import ast
import string
from typing import Dict, List, Optional, Set, Tuple, Union

from py2many.analysis import get_id, is_mutable, is_void_function
from py2many.ast_helpers import create_ast_node
from py2many.clike import class_for_typename
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstNotImplementedError
from py2many.tracer import defined_before, is_list

from .clike import CLikeTranspiler
from .inference import V_WIDTH_RANK
from .plugins import (
    ATTR_DISPATCH_TABLE,
    CLASS_DISPATCH_TABLE,
    DISPATCH_MAP,
    FUNC_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)

_is_mutable = is_mutable


def is_mutable(scopes, target: str) -> bool:
    if target == "_":
        return False
    return _is_mutable(scopes, target)


_create_ast_node = create_ast_node


def create_ast_node(code, at_node=None) -> ast.AST:
    res = _create_ast_node(code, at_node=at_node)
    if isinstance(res, ast.Expr):
        res = res.value
    return res


def is_dict(node: ast.AST) -> bool:
    if isinstance(node, (ast.Dict, ast.DictComp)):
        return True
    elif isinstance(node, ast.Call) and get_id(node.func) == "dict":
        return True
    elif isinstance(node, ast.Assign):
        return is_dict(node.value)
    elif isinstance(node, ast.Name):
        if hasattr(node, "scopes"):
            var: ast.AST = node.scopes.find(get_id(node))
            return (
                hasattr(var, "assigned_from")
                and not isinstance(var.assigned_from, ast.FunctionDef)
                and not isinstance(var.assigned_from, ast.For)
                and is_dict(var.assigned_from.value)
            )
        return False
    else:
        return False


class VDictRewriter(ast.NodeTransformer):
    def visit_Call(self, node: ast.Call) -> ast.Call:
        if (
            isinstance(node.func, ast.Attribute) and node.func.attr == "values"
        ):  # and is_dict(node.func.value):
            new_node: ast.Call = create_ast_node("a.keys().map(a[it])", at_node=node)
            new_node.func.value.func.value = node.func.value
            new_node.args[0].value = node.func.value
            return new_node
        return node


class VComprehensionRewriter(ast.NodeTransformer):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.redirects: Dict[str, str] = {}

    def visit_Name(self, node: ast.Name) -> Union[ast.Name, ast.Subscript]:
        if node.id in self.redirects:
            return create_ast_node(self.redirects[node.id], at_node=node)
        return node

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> ast.Call:
        new_node = None
        for comp in node.generators:
            if isinstance(comp.target, ast.Name):
                self.redirects[comp.target.id] = "it"
            elif isinstance(comp.target, ast.Tuple):
                for idx, elem in enumerate(comp.target.elts):
                    assert isinstance(elem, ast.Name)
                    self.redirects[elem.id] = f"it[{idx}]"
            else:
                raise AstNotImplementedError(
                    f"Unknown target type {type(node.target).__qualname__}", node
                )

            subnode = comp.iter

            for cmp in comp.ifs:
                chain = create_ast_node("placeholder.filter(placeholder)", at_node=node)
                chain.func.value = subnode
                chain.args[0] = cmp
                subnode = chain

            chain = create_ast_node("placeholder.map(placeholder)", at_node=node)
            chain.func.value = subnode
            chain.args[0] = node.elt
            subnode = chain

            if new_node is None:
                new_node = subnode
            else:
                new_node.args[0] = subnode

        self.visit(new_node)
        self.redirects.clear()
        return new_node

    def visit_ListComp(self, node: ast.ListComp) -> ast.Call:
        return self.visit_GeneratorExp(node)

    def visit_SetComp(self, node: ast.SetComp) -> ast.Call:
        # V doesn't have sets, so set comprehensions become array comprehensions
        return self.visit_GeneratorExp(node)


class VNoneCompareRewriter(ast.NodeTransformer):
    def visit_Compare(self, node: ast.Compare):
        left: ast.AST = self.visit(node.left)
        right: ast.AST = self.visit(node.comparators[0])
        if (
            isinstance(right, ast.Constant)
            and right.value is None
            and isinstance(left, ast.Constant)
            and isinstance(left.value, int)
        ):
            # Convert None to 0 to compare vs int
            right.value = 0
        return node


class VTranspiler(CLikeTranspiler):
    NAME: str = "v"

    ALLOW_MODULE_LIST: List[str] = ["math"]

    def __init__(self, indent: int = 2):
        super().__init__()
        self._headers = set()
        self._indent = " " * indent
        CLikeTranspiler._default_type = "any"
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE

    def indent(self, code: str, level=1) -> str:
        return self._indent * level + code

    def usings(self):
        usings: List[str] = sorted(list(set(self._usings)))
        uses: str = "\n".join(f"import {mod}" for mod in usings)
        # Module statement needs to be here as uses is applied to the top of the file
        # but V expects the module statement to be at the top.
        return f"[translated]\nmodule main\n{uses}"

    @classmethod
    def _combine_value_index(cls, value_type, index_type) -> str:
        return f"{value_type}{index_type}"

    def comment(self, text: str) -> str:
        return f"// {text}\n"

    def _import(self, name: str) -> str:
        # Suppress all imports for now until a reliable way to differentiate submodule imports is used.
        return ""

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        # Suppress all imports for now until a reliable way to differentiate submodule imports is used.
        return ""  # f"import {module_name} {{{' '.join(names)}}}"

    def visit_arg(self, node) -> Tuple[Optional[str], str]:
        id = get_id(node)
        if id == "self":
            return (None, "self")
        typename = ""
        if node.annotation:
            typename = self._typename_from_annotation(node)
        if is_mutable(node.scopes, id):
            id = f"mut {id}"
        return (typename, id)

    def visit_FunctionDef(self, node) -> str:
        signature = ["fn"]
        is_class_method: bool = False
        if (
            hasattr(node, "scopes") and node.scopes is not None
            and len(getattr(node, "scopes", [])) > 1
            and isinstance(getattr(node, "scopes", [])[-2], ast.ClassDef)
        ):
            is_class_method = True

        # Check if this is a generator function
        is_generator = self._is_generator_function(node)

        generics: Set[str] = set()
        args: List[Tuple[str, str]] = []
        receiver: str = ""
        for arg in node.args.args:
            typename, id = self.visit(arg)
            if typename is None and is_class_method:  # receiver
                receiver = id
                continue
            elif len(typename) == 1 and typename.isupper():
                generics.add(typename)
            args.append((typename, id))

        if is_class_method:
            signature.append(f"({receiver} {get_id(getattr(node, 'scopes', [])[-2])})")
        signature.append(node.name)

        str_args: List[str] = []
        for typename, id in args:
            if typename == "":
                for c in string.ascii_uppercase:
                    if c not in generics:
                        generics.add(c)
                        typename = c
                        break
            if typename == "":
                raise AstNotImplementedError(
                    "Cannot use more than 26 generics in a function.", node
                )

            str_args.append(f"{id} {typename}")

        # For generator functions, add channel parameter
        if is_generator:
            # Determine the yield type from annotations or use 'any'
            yield_type = "any"
            if node.returns:
                # For generators, returns annotation indicates the yield type
                yield_type = self._typename_from_annotation(node, attr="returns")
            str_args.append(f"ch chan {yield_type}")

        signature.append(f"({', '.join(str_args)})")

        # Generator functions don't return a value directly
        if not is_void_function(node) and not is_generator:
            signature.append(self._typename_from_annotation(node, attr="returns"))
        elif is_generator:
            # Generators return void in V (they send values via channel)
            pass

        body = "\n".join([self.indent(self.visit(n)) for n in node.body])
        return f"{' '.join(signature)} {{\n{body}\n}}"

    def visit_Return(self, node: ast.Return) -> str:
        if node.value:
            ret: str = self.visit(node.value)
            return f"return {ret}"
        return "return"

        if node.value:
            return f"return {self.visit(node.value)}"
        return "return"

    def visit_Lambda(self, node: ast.Lambda) -> str:
        # Convert lambda to inline function call
        args = []
        for arg in node.args.args:
            arg_name = get_id(arg)
            if is_mutable(node.scopes, arg_name):
                arg_name = f"mut {arg_name}"
            args.append(arg_name)

        args_str = ", ".join(args)
        body = self.visit(node.body)

        # V doesn't support lambdas directly, so we'll use an anonymous function
        return f"fn ({args_str}) {{ return {body} }}"

    def visit_Attribute(self, node: ast.Attribute) -> str:
        attr: str = node.attr

        value_id: str = self.visit(node.value)

        if is_list(node.value):
            if node.attr == "append":
                return f"{value_id} <<"
        if not value_id:
            value_id: str = ""
        ret: str = f"{value_id}.{attr}"
        if ret in self._attr_dispatch_table:
            return self._attr_dispatch_table[ret](self, node)
        return value_id + "." + attr

    def _visit_object_literal(self, node, fname: str, fndef: ast.ClassDef) -> str:
        vargs: List[str] = []  # visited args
        if not hasattr(fndef, "declarations"):
            raise Exception("Missing declarations")
        if node.args:
            for arg, decl in zip(node.args, fndef.declarations.keys()):
                arg: str = self.visit(arg)
                vargs += [f"{decl}: {arg}"]
        if node.keywords:
            for kw in node.keywords:
                value: str = self.visit(kw.value)
                vargs += [f"{kw.arg}: {value}"]
        args: str = ", ".join(vargs)
        return f"{fname}{{{args}}}"

    def visit_Call(self, node: ast.Call) -> str:
        fname: str = self.visit(node.func)
        if hasattr(node, "scopes"):
            fndef: ast.AST = node.scopes.find(fname)
        else:
            fndef = None

        if isinstance(fndef, ast.ClassDef):
            return self._visit_object_literal(node, fname, fndef)

        # Check if this is a generator function call
        is_generator_call = False
        if isinstance(fndef, ast.FunctionDef):
            is_generator_call = self._is_generator_function(fndef)

        vargs: List[str] = []

        for idx, arg in enumerate(node.args):
            if hasattr(fndef, "args") and is_mutable(
                fndef.scopes, fndef.args.args[idx].arg
            ):
                vargs.append(f"mut {self.visit(arg)}")
            else:
                vargs.append(self.visit(arg))
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret: Optional[str] = self._dispatch(node, fname, vargs)
        if ret is not None:
            return ret

        # Handle generator calls
        if is_generator_call:
            # Create channel and spawn
            args_str = ", ".join(vargs) if vargs else ""
            # We need to return something that can be iterated
            # For now, we'll create a pattern that spawns the generator
            # The caller will need to handle the channel iteration
            return f"spawn {fname}({args_str}, ch)"

        if vargs:
            args = ", ".join(vargs)
        else:
            args = ""
        return f"{fname}({args})"

    def visit_For(self, node: ast.For) -> str:
        target: str = self.visit(node.target)
        buf: List[str] = []
        if (
            isinstance(node.iter, ast.Call)
            and get_id(node.iter.func) == "range"
            and len(node.iter.args) == 3
        ):
            start: str = self.visit(node.iter.args[0])
            end: str = self.visit(node.iter.args[1])
            step: str = self.visit(node.iter.args[2])
            buf.append(
                f"for {target} := {start}; {target} < {end}; {target} += {step} {{"
            )
        else:
            it: str = self.visit(node.iter)
            buf.append(f"for {target} in {it} {{")
        buf.extend(
            [self.indent(self.visit(c), level=getattr(node, "level", 0) + 1) for c in node.body]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_While(self, node: ast.While) -> str:
        buf: List[str] = []
        if isinstance(node.test, ast.Constant) and node.test.value == True:
            buf.append("for {")
        else:
            buf.append(f"for {self.visit(node.test)} {{")
        buf.extend(
            [self.indent(self.visit(n), level=getattr(node, "level", 0) + 1) for n in node.body]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_Bytes(self, node: ast.Constant) -> str:
        if not node.s:
            return "[]byte{}"

        chars: List[str] = []
        chars.append(f"byte({hex(node.s[0])})")
        for c in node.s[1:]:
            chars.append(hex(c))
        return f"[{', '.join(chars)}]"

    def visit_If(self, node: ast.If) -> str:
        body_vars: Set[str] = {get_id(v) for v in getattr(node, "scopes", [None])[-1].body_vars}
        orelse_vars: Set[str] = {get_id(v) for v in getattr(node, "scopes", [None])[-1].orelse_vars}
        node.common_vars = body_vars.intersection(orelse_vars)

        body: str = "\n".join(
            [
                self.indent(self.visit(child), level=getattr(node, "level", 0) + 1)
                for child in node.body
            ]
        )
        orelse: str = "\n".join(
            [
                self.indent(self.visit(child), level=getattr(node, "level", 0) + 1)
                for child in node.orelse
            ]
        )
        test: str = self.visit(node.test)
        if node.orelse:
            orelse = self.indent(f"else {{\n{orelse}\n}}", level=getattr(node, "level", 0))
        else:
            orelse = ""
        return f"if {test} {{\n{body}\n}}\n{orelse}"

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, (ast.Call, ast.Num)):
                # Shortcut if parenthesis are not needed
                return f"-{self.visit(node.operand)}"
            else:
                return f"-({self.visit(node.operand)})"
        else:
            return super().visit_UnaryOp(node)

    def visit_ClassDef(self, node) -> str:
        extractor = DeclarationExtractor(VTranspiler())
        extractor.visit(node)
        node.declarations = declarations = extractor.get_declarations()
        node.declarations_with_defaults = extractor.get_declarations_with_defaults()
        node.class_assignments = extractor.class_assignments
        ret = super().visit_ClassDef(node)
        if ret is not None:
            return ret

        decorators = [get_id(d) for d in node.decorator_list]

        decorators = [
            class_for_typename(t, None, self._imported_names) for t in decorators
        ]
        for d in decorators:
            if d in CLASS_DISPATCH_TABLE:
                ret = CLASS_DISPATCH_TABLE[d](self, node)
                if ret is not None:
                    return ret

        fields = []
        if declarations:
            fields.append("pub mut:")
        index = 0
        for declaration, typename in declarations.items():
            if typename == None:
                typename = f"ST{index}"
                index += 1
            fields.append(f"{declaration} {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = node.name

        struct_def = "pub struct {0} {{\n{1}\n}}\n\n".format(
            node.name, "\n".join(fields)
        )
        buf = [self.visit(b) for b in node.body]
        buf_str = "\n".join(buf)
        return f"{struct_def}{buf_str}"

    def visit_IntEnum(self, node: ast.ClassDef) -> str:
        # V has enums, but they require a name and don't have explicit values
        # We'll create a struct with constants instead
        fields = []
        for item in node.body:
            if isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        if isinstance(item.value, ast.Constant):
                            fields.append(f"    {target.id} = {item.value.value}")
                        else:
                            fields.append(f"    {target.id}")

        # Use struct instead of unnamed enum
        struct_def = f"struct {node.name} {{\n" + "\n".join(fields) + "\n}"
        return struct_def

    def visit_IntFlag(self, node: ast.ClassDef) -> str:
        # V doesn't have flag enums, but we can use a struct with constants
        fields = []
        for item in node.body:
            if isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        if isinstance(item.value, ast.Constant):
                            fields.append(f"    {target.id} = {item.value.value}")
                        else:
                            fields.append(f"    {target.id}")

        # Use struct instead of unnamed enum
        struct_def = f"struct {node.name} {{\n" + "\n".join(fields) + "\n}"
        return struct_def

    def visit_StrEnum(self, node: ast.ClassDef) -> str:
        # V doesn't have string enums, so we'll use a struct with string constants
        fields = []
        for item in node.body:
            if isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        if isinstance(item.value, ast.Constant):
                            fields.append(f'    {target.id} = "{item.value.value}"')
                        else:
                            fields.append(f"    {target.id}")

        # Since V doesn't support string enums, we'll use a struct
        struct_fields = "\n".join(
            f"    {field.split('=')[0].strip()} string" for field in fields
        )
        struct_init = "\n".join(
            f"    {field.split('=')[0].strip()}: {field.split('=')[1].strip()}"
            for field in fields
            if "=" in field
        )

        struct_def = f"struct StrEnum {{\n{struct_fields}\n}}\n\n"
        init_def = f"const (\n{struct_init}\n)"
        return f"{struct_def}{init_def}"

    def visit_List(self, node: ast.List) -> str:
        elements: List[str] = [self.visit(e) for e in node.elts]
        elements: str = ", ".join(elements)
        return f"[{elements}]"

    def visit_Set(self, node: ast.Set) -> str:
        # V doesn't have built-in sets, use arrays as a workaround
        elements: List[str] = [self.visit(e) for e in node.elts]
        elements_str: str = ", ".join(elements)
        return f"[{elements_str}]"

    def visit_Dict(self, node: ast.Dict) -> str:
        keys: List[str] = [self.visit(k) for k in node.keys]
        values: List[str] = [self.visit(k) for k in node.values]
        kv_pairs: str = " ".join([f"{k}: {v}" for k, v in zip(keys, values)])
        return f"{{{kv_pairs}}}"

    def visit_Subscript(self, node: ast.Subscript) -> str:
        value: str = self.visit(node.value)
        index: str = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in self._container_type_map:
                value = self._container_type_map[value]
            if value == "Tuple":
                return f"({index})"
            return f"{value}[{index}]"
        return f"{value}[{index}]"

    def visit_Index(self, node: ast.Index) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node: ast.Slice) -> str:
        lower: str = ""
        if node.lower:
            lower = self.visit(node.lower)
        upper: str = ""
        if node.upper:
            upper = self.visit(node.upper)

        return f"{lower}..{upper}"

    def visit_Elipsis(self, node) -> str:
        return ""

    def visit_Tuple(self, node: ast.Tuple) -> str:
        # V does not have tuples, so treat them as same.
        return self.visit_List(node)

    def visit_Try(self, node: ast.Try, finallybody: bool = None) -> str:
        self._usings.add("div72.vexc")
        buf = []
        buf.append("if C.try() {")
        buf.extend(map(self.visit, node.body))
        buf.append("vexc.end_try()")
        buf.append("}")
        if len(node.handlers) == 1 and not node.handlers[0].type:
            # Just except:
            buf.append("else {")
            buf.extend(map(self.visit, node.handlers[0].body))
            buf.append("}")
        elif node.handlers:
            buf.append("else {")
            buf.append("match vexc.get_curr_exc().name {")
            has_else: bool = False
            for handler in node.handlers:
                buf2 = self.visit(handler)
                if buf2.startswith("else"):
                    has_else = True
                buf.append(buf2)
            if not has_else:
                buf.append("else {}")
            buf.append("}")
            buf.append("}")
        if node.finalbody:
            buf.extend(map(self.visit, node.finalbody))
        return "\n".join(buf)

    def visit_ExceptHandler(self, node) -> str:
        buf = []
        if node.type:
            buf.append(f"'{get_id(node.type)}' {{")
        else:
            buf.append("else {")
        if node.name:
            buf.append(f"{node.name} := vexc.get_curr_exc()")
        buf.extend(map(self.visit, node.body))
        buf.append("}")
        return "\n".join(buf)

    def visit_Assert(self, node: ast.Assert) -> str:
        return f"assert {self.visit(node.test)}"

    def visit_AnnAssign(self, node: ast.AnnAssign) -> str:
        target, type_str, val = super().visit_AnnAssign(node)
        kw: str = "mut " if is_mutable(node.scopes, target) else ""
        if isinstance(node.value, ast.List):
            if node.value.elts:
                elts: List[str] = []
                if type_str[2:] in V_WIDTH_RANK:
                    elts.append(f"{type_str[2:]}({self.visit(node.value.elts[0])})")
                else:
                    elts.append(self.visit(node.value.elts[0]))
                elts.extend(map(self.visit, node.value.elts[1:]))
                return f"{kw}{target} := [{', '.join(elts)}]"
            return f"{kw}{target} := {type_str}{{}}"
        else:
            return f"{kw}{target} := {val}"

    def visit_Assign(self, node: ast.Assign) -> str:
        assign: List[str] = []
        use_temp: bool = len(node.targets) > 1 and isinstance(node.value, ast.Call)
        if use_temp:
            assign.append(f"mut tmp := {self.visit(node.value)}")
        for target in node.targets:
            if hasattr(node, "scopes"):
                kw: str = "mut " if is_mutable(node.scopes, get_id(target)) else ""
            else:
                kw: str = "mut "  # Default to mut for nodes without scopes
            if use_temp:
                value: str = "tmp"
            else:
                value: str = self.visit(node.value)

            if isinstance(target, (ast.Tuple, ast.List)):
                value = value[1:-1]
                subtargets: List[str] = []
                op: str = ":="
                for subtarget in target.elts:
                    if hasattr(node, "scopes"):
                        subkw: str = (
                            "mut " if is_mutable(node.scopes, get_id(subtarget)) else ""
                        )
                        definition: Optional[ast.AST] = node.scopes.parent_scopes.find(
                            get_id(subtarget)
                        ) or node.scopes.find(get_id(subtarget))
                    else:
                        subkw: str = "mut "
                        definition: Optional[ast.AST] = None
                    subtargets.append(f"{subkw}{self.visit(subtarget)}")
                    if definition is not None and defined_before(definition, subtarget):
                        op = "="
                    elif op == "=":
                        raise AstNotImplementedError(
                            "Mixing declarations and assignment in the same statement is unsupported.",
                            node,
                        )
                assign.append(f"{', '.join(subtargets)} {op} {value}")
            elif isinstance(target, (ast.Subscript, ast.Attribute)):
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            elif isinstance(target, ast.Name) and defined_before(
                getattr(node.scopes, "parent_scopes", None).find(target.id)
                or getattr(node.scopes, "find", lambda x: None)(target.id),
                node,
            ):
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            else:
                target: str = self.visit(target)

                assign.append(f"{kw}{target} := {value}")
        return "\n".join(assign)

    def visit_AugAssign(self, node: ast.AugAssign) -> str:
        target: str = self.visit(node.target)
        op: str = self.visit(node.op)
        val: str = self.visit(node.value)
        return f"{target} {op}= {val}"

    def visit_Delete(self, node: ast.Delete) -> str:
        # V supports delete() function for maps and arrays
        targets = []
        for target in node.targets:
            targets.append(f"delete({self.visit(target)})")
        return "\n".join(targets)

    def visit_Raise(self, node: ast.Raise) -> str:
        self._usings.add("div72.vexc")
        name: str = f'"{get_id(node.exc)}"'
        msg: str = '""'
        if node.exc is None:
            return "vexc.raise('Exception', '')"
        elif isinstance(node.exc, ast.Call):
            name = f'"{get_id(node.exc.func)}"'
            if node.exc.args:
                msg = self.visit(node.exc.args[0])
        return f"vexc.raise({name}, {msg})"

    def visit_With(self, node: ast.With) -> str:
        # V doesn't have 'with' statement, but we can use defer for cleanup
        # For now, we'll just generate the body and add defer if needed
        buf = []

        # Process items
        for item in node.items:
            if item.optional_vars:
                # Assign context manager to variable
                target = self.visit(item.optional_vars)
                context = self.visit(item.context_expr)
                buf.append(f"{target} := {context}")
                # Add defer for __exit__ if it exists
                buf.append(f"defer {{ {target}.__exit__() }}")
            else:
                # Just call the context manager
                context = self.visit(item.context_expr)
                buf.append(f"defer {{ {context}.__exit__() }}")
                buf.append(f"{context}.__enter__()")

        # Process body
        for stmt in node.body:
            buf.append(self.visit(stmt))

        return "\n".join(buf)

    def visit_Await(self, node: ast.Await) -> str:
        raise AstNotImplementedError("asyncio is not supported.", node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> str:
        # V doesn't have async/await, but we can convert async functions to regular ones
        # with warnings about lost async semantics
        # The function body will be processed normally, but async operations will be converted
        import warnings

        warnings.warn(
            f"Async function '{node.name}' converted to sync. Async semantics lost."
        )

        # Convert AsyncFunctionDef to FunctionDef for processing
        # Both have the same structure except the type
        func_node = ast.FunctionDef(
            name=node.name,
            args=node.args,
            body=node.body,
            decorator_list=node.decorator_list,
            returns=node.returns,
            type_comment=node.type_comment,
            lineno=node.lineno,
            col_offset=node.col_offset,
            end_lineno=node.end_lineno,
            end_col_offset=node.end_col_offset,
        )
        # Copy scopes from original node
        func_node.scopes = node.scopes

        return self.visit_FunctionDef(func_node)

    def visit_Yield(self, node: ast.Yield) -> str:
        # V doesn't have generators, so we use channels
        # The function should be converted to accept a channel parameter
        # yield value becomes: ch <- value
        if node.value:
            return f"ch <- {self.visit(node.value)}"
        return "ch <- 0"  # Empty yield

    def visit_DictComp(self, node: ast.DictComp) -> str:
        # V doesn't have dict comprehensions, but we can use map
        # For dict comprehension {k: v for ...}, we'll create a map
        # First, we need to handle the generators
        if not node.generators:
            return "{}"

        # For dict comp, we need special handling
        # Let's create a map using a loop
        if not node.generators:
            raise AstNotImplementedError("DictComp with no generators", node)

        buf = []

        # Infer types from the key and value expressions
        key_type = "any"
        value_type = "any"

        # Try to infer types from annotations if available
        if hasattr(node, "key_annotation"):
            key_type = self._typename_from_annotation(node, attr="key_annotation")
        if hasattr(node, "value_annotation"):
            value_type = self._typename_from_annotation(node, attr="value_annotation")

        buf.append(f"mut result = map[{key_type}]{value_type}{{}}")

        for comp in node.generators:
            target = comp.target
            iter_expr = comp.iter

            # Build the for loop
            if isinstance(target, ast.Name):
                target_name = target.id
                buf.append(f"for {target_name} in {self.visit(iter_expr)} {{")
            else:
                # Handle tuple unpacking
                buf.append(f"for {self.visit(target)} in {self.visit(iter_expr)} {{")

            # Add filters
            for if_clause in comp.ifs:
                buf.append(f"    if {self.visit(if_clause)} {{")

            # Add the dict assignment
            key = self.visit(node.key)
            value = self.visit(node.value)
            buf.append(f"        result[{key}] = {value}")

            # Close if blocks
            for _ in comp.ifs:
                buf.append("    }")

            buf.append("}")

        buf.append("result")
        return "\n".join(buf)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> str:
        # V doesn't have generators, so we'll use an array
        # This should be handled by VComprehensionRewriter, but if not:
        if not node.generators:
            raise AstNotImplementedError("GeneratorExp with no generators", node)

        buf = []
        buf.append("mut result = []")

        for comp in node.generators:
            target = comp.target
            iter_expr = comp.iter

            if isinstance(target, ast.Name):
                target_name = target.id
                buf.append(f"for {target_name} in {self.visit(iter_expr)} {{")
            else:
                buf.append(f"for {self.visit(target)} in {self.visit(iter_expr)} {{")

            for if_clause in comp.ifs:
                buf.append(f"    if {self.visit(if_clause)} {{")

            buf.append(f"        result << {self.visit(node.elt)}")

            for _ in comp.ifs:
                buf.append("    }")

            buf.append("}")

        buf.append("result")
        return "\n".join(buf)

    def visit_ListComp(self, node: ast.ListComp) -> str:
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_SetComp(self, node: ast.SetComp) -> str:
        # V doesn't have sets, so set comprehensions return arrays
        # The VComprehensionRewriter should handle this before it reaches here
        # If it reaches here, it means the rewriter didn't process it
        # So we fall back to the same logic as ListComp
        return self.visit_GeneratorExp(node)

    def visit_Global(self, node: ast.Global) -> str:
        # V doesn't have global keyword, but module-level variables are accessible
        # We'll just comment it out
        names = ", ".join(node.names)
        return f"// global {names}  // V doesn't support global keyword"

    def visit_Starred(self, node: ast.Starred) -> str:
        # V doesn't have starred expressions like Python
        # But in some contexts (like function calls), we can use array spread
        # For now, we'll just return the value without the star
        # This is a limitation, but better than throwing an error
        return self.visit(node.value) + " /* starred */"

    def visit_IfExp(self, node: ast.IfExp) -> str:
        body: str = self.visit(node.body)
        orelse: str = self.visit(node.orelse)
        test: str = self.visit(node.test)
        return f"if {test} {{ {body} }} else {{ {orelse} }}"

    def visit_NamedExpr(self, node: ast.NamedExpr) -> str:
        # V doesn't support walrus operator, but we can simulate it
        # For x := value, we'll generate: mut x = value; x
        target = self.visit(node.target)
        value = self.visit(node.value)

        # Check if variable is mutable
        kw = "mut " if is_mutable(node.scopes, get_id(node.target)) else ""

        # Return both the assignment and the variable name
        # This is used in expressions like: if (x := func()) is not None:
        # We'll need to handle this carefully in context
        return f"{kw}{target} := {value}"

    def visit_Nonlocal(self, node: ast.Nonlocal) -> str:
        # V doesn't have nonlocal keyword
        # Variables in V are accessible from nested functions if they're in the same scope
        names = ", ".join(node.names)
        return f"// nonlocal {names}  // V doesn't support nonlocal keyword"

    def visit_AsyncFor(self, node: ast.AsyncFor) -> str:
        # V doesn't support async/await, so we'll convert to regular for
        # WARNING: This loses async semantics - the iterator is assumed to be synchronous
        # For true async behavior, V uses channels and spawn
        target: str = self.visit(node.target)
        it: str = self.visit(node.iter)

        buf = []
        buf.append("// WARNING: async for converted to sync for")
        buf.append(f"for {target} in {it} {{")
        buf.extend(
            [self.indent(self.visit(c), level=getattr(node, "level", 0) + 1) for c in node.body]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_AsyncWith(self, node: ast.AsyncWith) -> str:
        # V doesn't support async/await, so we'll convert to regular with
        # Using defer for cleanup - most concise and idiomatic V approach
        # defer guarantees execution on function exit, even with panics/returns
        buf = []
        buf.append("// WARNING: async with converted to sync with defer")

        for item in node.items:
            if item.optional_vars:
                target = self.visit(item.optional_vars)
                context = self.visit(item.context_expr)
                buf.append(f"{target} := {context}")
                buf.append(f"defer {{ {target}.__exit__() }}")
            else:
                context = self.visit(item.context_expr)
                buf.append(f"defer {{ {context}.__exit__() }}")
                buf.append(f"{context}.__enter__()")

        for stmt in node.body:
            buf.append(self.visit(stmt))

        return "\n".join(buf)

    def visit_YieldFrom(self, node: ast.YieldFrom) -> str:
        # V doesn't have yield from, but we can iterate over another generator
        # yield from generator becomes:
        # for val in generator {
        #     ch <- val
        # }

        # Get the generator expression
        generator = self.visit(node.value)

        # We need to handle this carefully - the generator might be a function call
        # that returns a channel, or it might be an iterable
        # For now, we'll assume it's a generator that needs to be spawned

        buf = []
        buf.append(f"// yield from {generator}")
        buf.append(f"for val in {generator} {{")
        buf.append("    ch <- val")
        buf.append("}")

        return "\n".join(buf)
