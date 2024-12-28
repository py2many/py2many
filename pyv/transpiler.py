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
        var: ast.AST = node.scopes.find(get_id(node))
        return (
            hasattr(var, "assigned_from")
            and not isinstance(var.assigned_from, ast.FunctionDef)
            and not isinstance(var.assigned_from, ast.For)
            and is_dict(var.assigned_from.value)
        )
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
            node.scopes is not None
            and len(node.scopes) > 1
            and isinstance(node.scopes[-2], ast.ClassDef)
        ):
            is_class_method = True

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
            signature.append(f"({receiver} {get_id(node.scopes[-2])})")
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
        signature.append(f"({', '.join(str_args)})")

        if not is_void_function(node):
            signature.append(self._typename_from_annotation(node, attr="returns"))

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
        raise AstNotImplementedError("Lambdas are not supported yet.", node)

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
            for arg, decl in zip(node.args, fndef.declaration.keys()):
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
        fndef: ast.AST = node.scopes.find(fname)

        if isinstance(fndef, ast.ClassDef):
            return self._visit_object_literal(node, fname, fndef)

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
            [self.indent(self.visit(c), level=node.level + 1) for c in node.body]
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
            [self.indent(self.visit(n), level=node.level + 1) for n in node.body]
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
        body_vars: Set[str] = {get_id(v) for v in node.scopes[-1].body_vars}
        orelse_vars: Set[str] = {get_id(v) for v in node.scopes[-1].orelse_vars}
        node.common_vars = body_vars.intersection(orelse_vars)

        body: str = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.body
            ]
        )
        orelse: str = "\n".join(
            [
                self.indent(self.visit(child), level=node.level + 1)
                for child in node.orelse
            ]
        )
        test: str = self.visit(node.test)
        if node.orelse:
            orelse = self.indent(f"else {{\n{orelse}\n}}", level=node.level)
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
        raise AstNotImplementedError("Enums are not supported yet.", node)

    def visit_IntFlag(self, node: ast.ClassDef) -> str:
        raise AstNotImplementedError("Enums are not supported yet.", node)

    def visit_StrEnum(self, node: ast.ClassDef) -> str:
        raise AstNotImplementedError("String enums are not supported in V.", node)

    def visit_List(self, node: ast.List) -> str:
        elements: List[str] = [self.visit(e) for e in node.elts]
        elements: str = ", ".join(elements)
        return f"[{elements}]"

    def visit_Set(self, node: ast.Set) -> str:
        raise AstNotImplementedError("Sets are not implemented in V yet.", node)

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
            kw: str = "mut " if is_mutable(node.scopes, get_id(target)) else ""
            if use_temp:
                value: str = "tmp"
            else:
                value: str = self.visit(node.value)

            if isinstance(target, (ast.Tuple, ast.List)):
                value = value[1:-1]
                subtargets: List[str] = []
                op: str = ":="
                for subtarget in target.elts:
                    subkw: str = (
                        "mut " if is_mutable(node.scopes, get_id(subtarget)) else ""
                    )
                    subtargets.append(f"{subkw}{self.visit(subtarget)}")
                    definition: Optional[ast.AST] = node.scopes.parent_scopes.find(
                        get_id(subtarget)
                    ) or node.scopes.find(get_id(subtarget))
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
                node.scopes.parent_scopes.find(target.id)
                or node.scopes.find(target.id),
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
        raise AstNotImplementedError("`delete` statements are not supported yet.", node)

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
        raise AstNotImplementedError("`with` statements are not supported yet.", node)

    def visit_Await(self, node: ast.Await) -> str:
        raise AstNotImplementedError("asyncio is not supported.", node)

    def visit_AsyncFunctionDef(self, node: ast.FunctionDef) -> str:
        raise AstNotImplementedError("asyncio is not supported.", node)

    def visit_Yield(self, node: ast.Yield) -> str:
        raise AstNotImplementedError("Generators are not supported yet.", node)

    def visit_DictComp(self, node: ast.DictComp) -> str:
        raise AstNotImplementedError("Dict comprehensions are not supported yet.", node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> str:
        raise AstNotImplementedError(
            "Comprehensions should have been handled in the rewriter.", node
        )

    def visit_ListComp(self, node: ast.ListComp) -> str:
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_Global(self, node: ast.Global) -> str:
        raise AstNotImplementedError("Globals are not supported yet.", node)

    def visit_Starred(self, node: ast.Starred) -> str:
        raise AstNotImplementedError("Starred expressions are not supported yet.", node)

    def visit_IfExp(self, node: ast.IfExp) -> str:
        body: str = self.visit(node.body)
        orelse: str = self.visit(node.orelse)
        test: str = self.visit(node.test)
        return f"if {test} {{ {body} }} else {{ {orelse} }}"
