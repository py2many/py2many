import ast
import ast as py_ast
import re
import string
from typing import Dict, List, Optional, Set, Tuple, Union

from py2many.analysis import get_id, is_generator_function, is_mutable, is_void_function
from py2many.ast_helpers import create_ast_node
from py2many.clike import class_for_typename
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstNotImplementedError
from py2many.tracer import defined_before, is_list

from .clike import CLikeTranspiler
from .inference import V_WIDTH_RANK, get_inferred_v_type
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


def create_ast_node(code, at_node=None) -> py_ast.AST:
    res = _create_ast_node(code, at_node=at_node)
    if isinstance(res, py_ast.Expr):
        res = res.value
    return res


def is_dict(node: py_ast.AST) -> bool:
    if isinstance(node, (py_ast.Dict, py_ast.DictComp)):
        return True
    elif isinstance(node, py_ast.Call) and get_id(node.func) == "dict":
        return True
    elif isinstance(node, py_ast.Assign):
        return is_dict(node.value)
    elif isinstance(node, py_ast.Name):
        if hasattr(node, "scopes"):
            var: py_ast.AST = node.scopes.find(get_id(node))
            return (
                hasattr(var, "assigned_from")
                and not isinstance(var.assigned_from, py_ast.FunctionDef)
                and not isinstance(var.assigned_from, py_ast.For)
                and is_dict(var.assigned_from.value)
            )
        return False
    else:
        return False


class VDictRewriter(py_ast.NodeTransformer):
    def visit_Call(self, node: py_ast.Call) -> py_ast.Call:
        if (
            isinstance(node.func, py_ast.Attribute) and node.func.attr == "values"
        ):  # and is_dict(node.func.value):
            new_node: py_ast.Call = create_ast_node("a.keys().map(a[it])", at_node=node)
            new_node.func.value.func.value = node.func.value
            new_node.args[0].value = node.func.value
            return new_node
        return node


class VComprehensionRewriter(py_ast.NodeTransformer):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.redirects: Dict[str, str] = {}

    def visit_Name(self, node: py_ast.Name) -> Union[py_ast.Name, py_ast.Subscript]:
        if node.id in self.redirects:
            return create_ast_node(self.redirects[node.id], at_node=node)
        return node

    def visit_GeneratorExp(self, node: py_ast.GeneratorExp) -> py_ast.Call:
        new_node = None
        for comp in node.generators:
            if isinstance(comp.target, py_ast.Name):
                self.redirects[comp.target.id] = "it"
            elif isinstance(comp.target, py_ast.Tuple):
                for idx, elem in enumerate(comp.target.elts):
                    assert isinstance(elem, py_ast.Name)
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

    def visit_ListComp(self, node: py_ast.ListComp) -> py_ast.Call:
        return self.visit_GeneratorExp(node)

    def visit_SetComp(self, node: py_ast.SetComp) -> py_ast.Call:
        # V doesn't have sets, so set comprehensions become array comprehensions
        return self.visit_GeneratorExp(node)


class VNoneCompareRewriter(py_ast.NodeTransformer):
    def visit_Compare(self, node: py_ast.Compare):
        left: py_ast.AST = self.visit(node.left)
        right: py_ast.AST = self.visit(node.comparators[0])
        if (
            isinstance(right, py_ast.Constant)
            and right.value is None
            and isinstance(left, py_ast.Constant)
            and isinstance(left.value, int)
        ):
            # Convert None to 0 to compare vs int
            right.value = 0
        return node


class VWalrusRewriter(py_ast.NodeTransformer):
    def _has_walrus(self, node):
        return any(isinstance(n, py_ast.NamedExpr) for n in py_ast.walk(node))

    def visit_Module(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_If(self, node):
        node.body = self._expand_body(node.body)
        node.orelse = self._expand_body(node.orelse)
        self.generic_visit(node)
        return node

    def visit_While(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def visit_For(self, node):
        node.body = self._expand_body(node.body)
        self.generic_visit(node)
        return node

    def _expand_body(self, body):
        if not body:
            return body
        new_body = []
        for stmt in body:
            if not self._has_walrus(stmt):
                new_body.append(stmt)
                continue

            assignments = []

            class WalrusExtractor(py_ast.NodeTransformer):
                def visit_NamedExpr(self, n):
                    n.value = self.visit(n.value)
                    assignments.append(
                        py_ast.Assign(
                            targets=[n.target], value=n.value, lineno=n.lineno
                        )
                    )
                    return n.target

            extractor = WalrusExtractor()

            if isinstance(stmt, py_ast.While) and self._has_walrus(stmt.test):
                new_test = extractor.visit(stmt.test)
                break_if = py_ast.If(
                    test=py_ast.UnaryOp(op=py_ast.Not(), operand=new_test),
                    body=[py_ast.Break()],
                    orelse=[],
                )
                stmt.test = py_ast.Constant(value=True, lineno=stmt.lineno)
                stmt.body = assignments + [break_if] + stmt.body
                new_body.append(stmt)
            else:
                # Transform the expressions in the statement
                if isinstance(stmt, py_ast.If):
                    stmt.test = extractor.visit(stmt.test)
                elif isinstance(stmt, py_ast.For):
                    stmt.iter = extractor.visit(stmt.iter)
                elif hasattr(stmt, "value"):
                    stmt.value = extractor.visit(stmt.value)
                elif hasattr(stmt, "test"):  # Assert
                    stmt.test = extractor.visit(stmt.test)

                new_body.extend(assignments)
                new_body.append(stmt)
        return new_body


class VTranspiler(CLikeTranspiler):
    NAME: str = "v"

    ALLOW_MODULE_LIST: List[str] = ["math"]

    def __init__(self, indent: int = 2):
        super().__init__()
        self._headers = set()
        self._indent = " " * indent
        CLikeTranspiler._default_type = ""
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        self._generated_code_has_any_type = False
        self._tmp_var_id = 0
        self._int_enums: Set[str] = set()
        self._str_enums: Set[str] = set()

    def indent(self, code: str, level=1) -> str:
        return self._indent * level + code

    def _new_tmp(self, prefix: str = "tmp") -> str:
        self._tmp_var_id += 1
        return f"__{prefix}{self._tmp_var_id}"

    def visit_Module(self, node: py_ast.Module) -> str:
        code = super().visit_Module(node)
        # Hack: Fix int(x) -> (x as int) for variables (Any casting)
        code = re.sub(r"CAST_INT\((.*?)\)", r"(\1 as int)", code)
        self._generated_code_has_any_type = re.search(r"\bAny\b", code) is not None
        return code

    def usings(self):
        usings: List[str] = sorted(list(set(self._usings)))
        uses: str = "\n".join(f"import {mod}" for mod in usings)
        buf = ["@[translated]", "module main"]
        if uses:
            buf.append(uses)
        if self._generated_code_has_any_type:
            buf.append("")
            buf.append("type AnyFn = fn (Any) Any")
            buf.append("type Any = bool | int | i64 | f64 | string | []byte | voidptr")
            buf.append("type List = []Any")
            buf.append("")
        return "\n".join(buf)

    @classmethod
    def _combine_value_index(cls, value_type, index_type) -> str:
        return f"{value_type}{index_type}"

    @classmethod
    def _visit_container_type(cls, typename: Tuple) -> str:
        value_type, index_type = typename
        if isinstance(index_type, list):
            index_type = ", ".join(index_type)
        return cls._combine_value_index(value_type, index_type)

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
        else:
            inferred = get_inferred_v_type(node)
            if inferred:
                typename = inferred

        if is_mutable(node.scopes, id):
            id = f"mut {id}"
        return (typename, id)

    def visit_JoinedStr(self, node: py_ast.JoinedStr) -> str:
        parts = []
        for val in node.values:
            if isinstance(val, py_ast.Constant):
                parts.append(str(val.value))
            elif isinstance(val, py_ast.FormattedValue):
                parts.append(f"${{{self.visit(val.value)}}}")
            else:
                parts.append(f"${{{self.visit(val)}}}")
        return f"'{''.join(parts)}'"

    def _infer_generator_yield_type(self, node: py_ast.FunctionDef) -> str:
        inferred: List[str] = []
        for child in py_ast.walk(node):
            if not isinstance(child, py_ast.Yield):
                continue
            if child.value is None:
                continue
            typename = get_inferred_v_type(child.value)
            if typename:
                inferred.append(typename)

        if not inferred:
            return "Any"

        # If all types match, use that.
        if all(t == inferred[0] for t in inferred):
            return inferred[0]

        # If all are numeric, pick the widest.
        ranks = [V_WIDTH_RANK.get(t, -1) for t in inferred]
        if all(r >= 0 for r in ranks):
            return inferred[ranks.index(max(ranks))]

        return "Any"

    def visit_FunctionDef(self, node) -> str:
        signature = ["fn"]
        is_class_method: bool = False
        class_node = None
        if (
            hasattr(node, "scopes")
            and node.scopes is not None
            and len(getattr(node, "scopes", [])) > 1
            and isinstance(getattr(node, "scopes", [])[-2], py_ast.ClassDef)
        ):
            is_class_method = True
            class_node = node.scopes[-2]

        # Check if this is a generator function
        is_generator = is_generator_function(node)

        generics: Set[str] = set()
        args: List[Tuple[str, str]] = []
        receiver: str = "self"
        for i, arg in enumerate(node.args.args):
            typename, id = self.visit(arg)

            if i == 0 and is_class_method:  # receiver
                receiver = id.replace("mut ", "")
                continue
            elif typename is not None and len(typename) == 1 and typename.isupper():
                generics.add(typename)
            args.append((typename, id))

        if node.args.vararg:
            typename, id = self.visit(node.args.vararg)
            if typename is not None:
                if typename.startswith("[]"):
                    typename = "..." + typename[2:]
                else:
                    typename = "..." + typename
            args.append((typename, id))

        fn_name = node.name
        is_init = fn_name == "__init__"
        is_del = fn_name == "__del__"

        if is_init and class_node:
            fn_name = f"new_{class_node.name.lower()}"
        elif is_del:
            fn_name = "free"

        if is_class_method and not is_init:
            signature.append(f"(mut {receiver} {get_id(class_node)})")

        signature.append(fn_name)

        str_args: List[str] = []
        for typename, id in args:
            if typename in {"", "...", "...Any"} or not typename:
                if is_class_method and not is_init:
                    typename = "Any" if typename in {"", "Any"} else "...Any"
                else:
                    for c in string.ascii_uppercase:
                        if c not in generics:
                            generics.add(c)
                            typename = c if typename in {"", "Any"} else f"...{c}"
                            break
            # Only raise if we still have an empty/starred-only type
            if typename in {"", "..."}:
                raise AstNotImplementedError(
                    "Cannot use more than 26 generics in a function.", node
                )

            str_args.append(f"{id} {typename}")

        if generics:
            signature.append(f"[{', '.join(sorted(list(generics)))}]")

        # NO channel parameter injection
        # if is_generator: ... (Removed)

        signature.append(f"({', '.join(str_args)})")

        # In V, return type comes AFTER the arguments
        ret = self._typename_from_annotation(node, attr="returns")
        if is_init and class_node:
            signature.append(class_node.name)
        elif (ret and ret != "void") or not is_void_function(node):
            if not ret or ret == "void":
                # Special case for context managers returning self
                if node.name == "__enter__" and is_class_method:
                    for stmt in node.body:
                        if (
                            isinstance(stmt, py_ast.Return)
                            and get_id(stmt.value) == receiver
                        ):
                            ret = get_id(class_node)
                            break

                if not ret or ret == "void":
                    # Fallback if annotation is missing but it's not void
                    ret = "Any"
            signature.append(ret)
        elif is_generator:
            # Generators return chan Any
            yield_type = self._infer_generator_yield_type(node)
            signature.append(f"chan {yield_type}")

        nested_fndefs = [
            n
            for n in node.body
            if isinstance(n, (py_ast.FunctionDef, py_ast.AsyncFunctionDef))
        ]
        body_nodes = [n for n in node.body if n not in nested_fndefs]

        nested_code = "\n".join(self.visit(n) for n in nested_fndefs)

        body_lines: List[str] = []

        if is_generator:
            yield_type = self._infer_generator_yield_type(node)
            body_lines.append(self.indent(f"ch := chan {yield_type}{{cap: 100}}"))

            # Capture args and receiver
            capture_list = ["ch"]
            if is_class_method:
                capture_list.append(receiver)
            for _, arg_id in args:
                capture_list.append(arg_id.replace("mut ", ""))

            capture_str = f"[{', '.join(capture_list)}]"

            body_lines.append(self.indent(f"spawn fn {capture_str}() {{"))
            body_lines.append(self.indent("defer { ch.close() }", level=2))

            # Add body with extra indent
            for n in body_nodes:
                visited = self.visit(n)
                # Indent each line
                for line in visited.splitlines():
                    body_lines.append(self.indent(line, level=2))

            body_lines.append(self.indent("}()"))
            body_lines.append(self.indent("return ch"))

        else:
            if is_init and class_node:
                body_lines.append(
                    self.indent(f"mut {receiver} := {class_node.name}{{}}")
                )

            body_lines.extend(self.indent(self.visit(n)) for n in body_nodes)

            if is_init and class_node:
                # Check for __post_init__
                # Only call if not already in body
                has_post_init = any(
                    isinstance(b, py_ast.FunctionDef) and b.name == "__post_init__"
                    for b in class_node.body
                )
                already_called = any(
                    isinstance(n, py_ast.Expr)
                    and isinstance(n.value, py_ast.Call)
                    and get_id(n.value.func) == f"{receiver}.__post_init__"
                    for n in body_nodes
                )
                if has_post_init and not already_called:
                    body_lines.append(self.indent(f"{receiver}.__post_init__()"))
                body_lines.append(self.indent(f"return {receiver}"))

        body = "\n".join(body_lines)

        func_code = f"{' '.join(signature)} {{\n{body}\n}}"
        if nested_code:
            return f"{nested_code}\n{func_code}"
        return func_code

    def visit_Return(self, node: py_ast.Return) -> str:
        if node.value:
            ret: str = self.visit(node.value)
            return f"return {ret}"
        return "return"

        return "return"

    def visit_Lambda(self, node) -> str:
        try:
            # Convert lambda to inline function call
            args_names = {get_id(arg) for arg in node.args.args}
            captured = set()
            for child in py_ast.walk(node.body):
                if isinstance(child, py_ast.Name) and isinstance(
                    child.ctx, py_ast.Load
                ):
                    name = get_id(child)
                    if name not in args_names:
                        # Check if it's defined in outer scopes
                        if hasattr(node, "scopes"):
                            definition = node.scopes.find(name)
                            if definition and not isinstance(
                                definition, (py_ast.Module, py_ast.FunctionDef)
                            ):
                                captured.add(name)

            capture_str = ""
            if captured:
                capture_str = f"[{', '.join(sorted(list(captured)))}] "

            callable_type = getattr(node, "callable_type", None)
            explicit_arg_types = []
            explicit_ret_type = None
            if callable_type and isinstance(callable_type, py_ast.Subscript):
                if (
                    isinstance(callable_type.slice, py_ast.Tuple)
                    and len(callable_type.slice.elts) == 2
                ):
                    args_node, ret_node = callable_type.slice.elts
                    if isinstance(args_node, py_ast.List):
                        explicit_arg_types = [
                            self._typename_from_type_node(e) for e in args_node.elts
                        ]
                    explicit_ret_type = self._typename_from_type_node(ret_node)

            args = []
            for i, arg in enumerate(node.args.args):
                arg_name = get_id(arg)
                typename = get_inferred_v_type(arg)
                if not typename and i < len(explicit_arg_types):
                    typename = explicit_arg_types[i]
                if not typename:
                    typename = "Any"
                if is_mutable(node.scopes, arg_name):
                    arg_name = f"mut {arg_name}"
                args.append(f"{arg_name} {typename}")

            args_str = ", ".join(args)
            body = self.visit(node.body)

            ret_type = get_inferred_v_type(node.body)
            if not ret_type:
                ret_type = explicit_ret_type if explicit_ret_type else "Any"

            # V doesn't support lambdas directly, so we'll use an anonymous function
            return f"fn {capture_str}({args_str}) {ret_type} {{ return {body} }}"
        except Exception:
            import traceback

            traceback.print_exc()
            raise

    def visit_Attribute(self, node: py_ast.Attribute) -> str:
        attr: str = node.attr

        value_id: str = self.visit(node.value)

        if is_list(node.value):
            if node.attr == "append":
                return f"{value_id} <<"
        if not value_id:
            value_id: str = ""
        ret: str = f"{value_id}.{attr}"
        if attr == "write" and (
            "os.open" in value_id or "os.create" in value_id or "f" == value_id
        ):
            # Special case for file write
            return f"{value_id}.write_string"
        if attr == "name" and "temp_file" in value_id:
            return "os.join_path(os.temp_dir(), 'temp_file')"
        if ret in self._attr_dispatch_table:
            return self._attr_dispatch_table[ret](self, node)

        if value_id in self._int_enums:
            attr = attr.lower()
        elif value_id in self._str_enums:
            value_id = value_id.lower()
            attr = attr.lower()

        return value_id + "." + attr

    def visit_Call(self, node: py_ast.Call) -> str:
        fname: str = self.visit(node.func)
        fndef: Optional[py_ast.AST] = None
        if hasattr(node, "scopes"):
            fndef = node.scopes.find(fname)

        if isinstance(fndef, py_ast.ClassDef):
            vargs = [self.visit(a) for a in node.args]
            if node.keywords:
                vargs += [f"{kw.arg}: {self.visit(kw.value)}" for kw in node.keywords]

            if vargs:
                return f"new_{fname.lower()}({', '.join(vargs)})"
            return f"{fname}{{}}"

        vargs: List[str] = []
        for idx, arg in enumerate(node.args):
            is_starred = isinstance(arg, py_ast.Starred)
            visited_arg = self.visit(arg)

            if visited_arg.startswith("fn ") or "fn [" in visited_arg:
                # Check if parameter is Any
                if (
                    hasattr(fndef, "args")
                    and not is_starred
                    and idx < len(fndef.args.args)
                ):
                    param = fndef.args.args[idx]
                    param_type = self._typename_from_annotation(param)
                    if param_type == "Any":
                        visited_arg = f"voidptr({visited_arg})"

            if (
                hasattr(fndef, "args")
                and not is_starred
                and idx < len(fndef.args.args)
                and is_mutable(fndef.scopes, fndef.args.args[idx].arg)
            ):
                vargs.append(f"mut {visited_arg}")
            else:
                vargs.append(visited_arg)
        if node.keywords:
            vargs += [self.visit(kw.value) for kw in node.keywords]

        ret: Optional[str] = self._dispatch(node, fname, vargs)
        if ret is not None:
            if "write_string" in ret:
                return f"{ret} or {{ panic(err) }}"
            return ret

        if fname.endswith(".read"):
            receiver = fname.rsplit(".", 1)[0]
            inferred = (
                get_inferred_v_type(node.func.value)
                if isinstance(node.func, py_ast.Attribute)
                else None
            )
            # Only map to os.read_file if we have a file_path and it's likely a file
            if inferred in {None, "Any", "os.File"} and node.scopes.find("file_path"):
                if not vargs:
                    return "(os.read_file(file_path) or { '' })"
                else:
                    return f"{receiver}.read_bytes({vargs[0]}).bytestr()"
        if fname.endswith(".write"):
            receiver = fname.rsplit(".", 1)[0]
            inferred = (
                get_inferred_v_type(node.func.value)
                if isinstance(node.func, py_ast.Attribute)
                else None
            )
            if inferred in {None, "Any", "os.File"}:
                return (
                    f"{receiver}.write_string({', '.join(vargs)}) or {{ panic(err) }}"
                )
        if fname.endswith(".clear"):
            receiver = fname.rsplit(".", 1)[0]
            return f"/* {receiver}.clear() */ {receiver} = {{}}"

        args_str = ", ".join(vargs)
        result = f"{fname}({args_str})"
        if "write_string" in result:
            return f"{result} or {{ panic(err) }}"
        return result

    def visit_Starred(self, node: py_ast.Starred) -> str:
        return f"...{self.visit(node.value)}"

    def visit_arguments(self, node: py_ast.arguments) -> Tuple[List[str], List[str]]:
        args = [self.visit(arg) for arg in node.args]
        if args == []:
            typenames, args = [], []
        else:
            typenames, args = map(list, zip(*args))

        if node.vararg:
            v_type, arg_name = self.visit(node.vararg)
            if v_type.startswith("[]"):
                v_type = v_type[2:]
            args.append(f"{arg_name} ...{v_type}")
            typenames.append(f"...{v_type}")

        return typenames, args

    def visit_For(self, node: py_ast.For) -> str:
        target: str = self.visit(node.target)
        buf: List[str] = []
        if (
            isinstance(node.iter, py_ast.Call)
            and get_id(node.iter.func) == "range"
            and len(node.iter.args) <= 3
        ):
            if len(node.iter.args) == 3:
                start: str = self.visit(node.iter.args[0])
                end: str = self.visit(node.iter.args[1])
                step: str = self.visit(node.iter.args[2])
                buf.append(
                    f"for {target} := {start}; {target} < {end}; {target} += {step} {{"
                )
            elif len(node.iter.args) == 2:
                start: str = self.visit(node.iter.args[0])
                end: str = self.visit(node.iter.args[1])
                buf.append(f"for {target} in {start} .. {end} {{")
            else:
                end: str = self.visit(node.iter.args[0])
                buf.append(f"for {target} in 0 .. {end} {{")
        else:
            iter_is_generator = False
            chan_var = ""

            if isinstance(node.iter, py_ast.Call) and hasattr(node.iter, "scopes"):
                fname = self.visit(node.iter.func)
                fndef = node.iter.scopes.find(fname)
                if isinstance(
                    fndef, (py_ast.FunctionDef, py_ast.AsyncFunctionDef)
                ) and is_generator_function(fndef):
                    iter_is_generator = True
                    chan_expr = self.visit(node.iter)
                    chan_var = self._new_tmp("gen")
                    buf.append(f"{chan_var} := {chan_expr}")
            elif isinstance(node.iter, py_ast.Name) and hasattr(node.iter, "scopes"):
                definition = node.iter.scopes.find(node.iter.id)
                assigned_from = getattr(definition, "assigned_from", None)
                call = getattr(assigned_from, "value", None) if assigned_from else None
                if isinstance(call, py_ast.Call) and hasattr(call, "scopes"):
                    fname = self.visit(call.func)
                    fndef = call.scopes.find(fname)
                    if isinstance(
                        fndef, (py_ast.FunctionDef, py_ast.AsyncFunctionDef)
                    ) and is_generator_function(fndef):
                        iter_is_generator = True
                        chan_var = self.visit(node.iter)

            if not iter_is_generator:
                iter_type = get_inferred_v_type(node.iter)
                if iter_type and "chan" in iter_type:
                    iter_is_generator = True
                    chan_var = self.visit(node.iter)

            if iter_is_generator:
                buf.append("for {")
                buf.append(
                    self.indent(
                        f"{target} := <-{chan_var} or {{ break }}",
                        level=getattr(node, "level", 0) + 1,
                    )
                )
            else:
                it: str = self.visit(node.iter)
                iter_type = get_inferred_v_type(node.iter)
                # it = f"{it}.iter()"
                buf.append(f"for {target} in {it} {{")
        buf.extend(
            [
                self.indent(self.visit(c), level=getattr(node, "level", 0) + 1)
                for c in node.body
            ]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_While(self, node: py_ast.While) -> str:
        buf: List[str] = []
        if isinstance(node.test, py_ast.Constant) and node.test.value is True:
            buf.append("for {")
        else:
            buf.append(f"for {self.visit(node.test)} {{")
        buf.extend(
            [
                self.indent(self.visit(n), level=getattr(node, "level", 0) + 1)
                for n in node.body
            ]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_Constant(self, node):
        val = node.value
        if val is None:
            return "none"
        elif isinstance(val, bool):
            return "true" if val else "false"
        elif isinstance(val, str):
            return repr(val)
        elif isinstance(val, (int, float, complex)):
            return str(val)
        elif isinstance(val, bytes):
            if not node.value:
                return "[]byte{}"

            chars = []
            chars.append(f"byte({hex(node.value[0])})")
            for c in node.value[1:]:
                chars.append(hex(c))
            return f"[{', '.join(chars)}]"
        elif val is Ellipsis:
            return ""
        return str(val)

    def visit_Bytes(self, node: py_ast.Constant) -> str:
        if not node.s:
            return "[]byte{}"

        chars: List[str] = []
        chars.append(f"byte({hex(node.s[0])})")
        for c in node.s[1:]:
            chars.append(hex(c))
        return f"[{', '.join(chars)}]"

    def visit_If(self, node: py_ast.If) -> str:
        body_vars: Set[str] = {
            get_id(v) for v in getattr(node, "scopes", [None])[-1].body_vars
        }
        orelse_vars: Set[str] = {
            get_id(v) for v in getattr(node, "scopes", [None])[-1].orelse_vars
        }
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
            orelse = self.indent(
                f"else {{\n{orelse}\n}}", level=getattr(node, "level", 0)
            )
        else:
            orelse = ""
        return f"if {test} {{\n{body}\n}}\n{orelse}"

    def visit_UnaryOp(self, node: py_ast.UnaryOp) -> str:
        if isinstance(node.op, py_ast.USub):
            if isinstance(node.operand, py_ast.Call) or self._is_number(node.operand):
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
        for declaration, typename in declarations.items():
            if typename in {None, "", "Any"}:
                typename = "Any"
            fields.append(f"{declaration} {typename}")

        for b in node.body:
            if isinstance(b, py_ast.FunctionDef):
                b.self_type = node.name

        struct_def = "pub struct {0} {{\n{1}\n}}\n\n".format(
            node.name, "\n".join(fields)
        )
        buf = [self.visit(b) for b in node.body]
        buf_str = "\n".join(buf)
        return f"{struct_def}{buf_str}"

    def visit_IntEnum(self, node: py_ast.ClassDef) -> str:
        self._int_enums.add(node.name)
        fields = []
        for item in node.body:
            if isinstance(item, py_ast.Assign):
                for target in item.targets:
                    if isinstance(target, py_ast.Name):
                        if isinstance(item.value, py_ast.Constant):
                            fields.append(
                                f"    {target.id.lower()} = {item.value.value}"
                            )
                        else:
                            fields.append(f"    {target.id.lower()}")
        return f"enum {node.name} {{\n" + "\n".join(fields) + "\n}\n"

    def visit_IntFlag(self, node: py_ast.ClassDef) -> str:
        return self.visit_IntEnum(node)

    def visit_StrEnum(self, node: py_ast.ClassDef) -> str:
        self._str_enums.add(node.name)
        # V doesn't have string enums, so we'll use a struct with string constants
        fields = []
        for item in node.body:
            if isinstance(item, py_ast.Assign):
                for target in item.targets:
                    if isinstance(target, py_ast.Name):
                        if isinstance(item.value, py_ast.Constant):
                            fields.append((target.id.lower(), f'"{item.value.value}"'))
                        else:
                            fields.append((target.id.lower(), None))

        struct_fields = "\n".join(f"    {name} string" for name, _ in fields)
        struct_init = ", ".join(f"{name}: {val}" for name, val in fields if val)

        struct_def = f"struct {node.name}_t {{\n{struct_fields}\n}}\n\n"
        init_def = f"const {node.name.lower()} = {node.name}_t {{ {struct_init} }}"
        return f"{struct_def}{init_def}"

    def visit_List(self, node: py_ast.List) -> str:
        if any(isinstance(e, py_ast.Starred) for e in node.elts):
            self._usings.add("arrays")
            # V uses arrays.concat(a, ...b) to concatenate arrays
            # We chain these calls for multiple elements/stars
            res = None
            for e in node.elts:
                if isinstance(e, py_ast.Starred):
                    starred_val = self.visit(e.value)
                    if res is None:
                        res = starred_val
                    else:
                        res = f"arrays.concat({res}, ...{starred_val})"
                else:
                    val = self.visit(e)
                    if res is None:
                        res = f"[{val}]"
                    else:
                        res = f"arrays.concat({res}, {val})"
            return res if res else "[]"

        elements: List[str] = [self.visit(e) for e in node.elts]
        elements_str: str = ", ".join(elements)
        return f"[{elements_str}]"

    def visit_Set(self, node: py_ast.Set) -> str:
        # V doesn't have built-in sets, use arrays as a workaround
        return self.visit_List(node)

    def visit_Dict(self, node: py_ast.Dict) -> str:
        keys: List[str] = [self.visit(k) for k in node.keys]
        values: List[str] = [self.visit(k) for k in node.values]
        kv_pairs: str = " ".join([f"{k}: {v}" for k, v in zip(keys, values)])
        return f"{{{kv_pairs}}}"

    def visit_Subscript(self, node: py_ast.Subscript) -> str:
        value: str = self.visit(node.value)
        index: str = self.visit(node.slice)
        if hasattr(node, "is_annotation"):
            if value in self._container_type_map:
                value = self._container_type_map[value]
            print(f"DEBUG: visit_Subscript value={value} index={index}")
            if value == "Tuple":
                return f"({index})"
            if value == "[]":
                return f"[]{index}"
            return f"{value}[{index}]"
        return f"{value}[{index}]"

    def visit_Index(self, node: py_ast.Index) -> str:
        return self.visit(node.value)

    def visit_Slice(self, node: py_ast.Slice) -> str:
        lower: str = ""
        if node.lower:
            lower = self.visit(node.lower)
        upper: str = ""
        if node.upper:
            upper = self.visit(node.upper)

        return f"{lower}..{upper}"

    def visit_Elipsis(self, node) -> str:
        return ""

    def visit_Tuple(self, node: py_ast.Tuple) -> str:
        # V does not have tuples, so treat them as same.
        return self.visit_List(node)

    def visit_Try(self, node: py_ast.Try, finallybody: bool = None) -> str:
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
            has_else = False
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

    def visit_Assert(self, node: py_ast.Assert) -> str:
        return f"assert {self.visit(node.test)}"

    def visit_AnnAssign(self, node: py_ast.AnnAssign) -> str:
        if isinstance(node.value, py_ast.Lambda) and hasattr(node, "annotation"):
            node.value.callable_type = node.annotation
        target, type_str, val = super().visit_AnnAssign(node)
        kw: str = "mut " if is_mutable(node.scopes, target) else ""
        if isinstance(node.value, py_ast.List):
            if node.value.elts:
                elts: List[str] = []
                if type_str[2:] in V_WIDTH_RANK:
                    elts.append(f"{type_str[2:]}({self.visit(node.value.elts[0])})")
                else:
                    elts.append(self.visit(node.value.elts[0]))
                elts.extend(map(self.visit, node.value.elts[1:]))
                return f"{kw}{target} := [{', '.join(elts)}]"
            if type_str:
                return f"{kw}{target} := {type_str}{{}}"
            return f"{kw}{target} := {val}"
        elif isinstance(node.value, py_ast.Dict):
            if not node.value.keys and type_str:
                return f"{kw}{target} := {type_str}{{}}"
            return f"{kw}{target} := {val}"
        else:
            return f"{kw}{target} := {val}"

    def visit_Assign(self, node: py_ast.Assign) -> str:
        assign: List[str] = []
        use_temp: bool = len(node.targets) > 1 and isinstance(node.value, py_ast.Call)
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

            if isinstance(target, (py_ast.Tuple, py_ast.List)):
                # Check for Starred expressions in subtargets
                starred_idx = -1
                for i, elt in enumerate(target.elts):
                    if isinstance(elt, py_ast.Starred):
                        if starred_idx != -1:
                            raise AstNotImplementedError(
                                "Only one starred expression allowed in assignment",
                                node,
                            )
                        starred_idx = i

                if starred_idx != -1:
                    # Extended unpacking: a, *b, c = x
                    # We need a temporary variable if 'value' is complex
                    tmp_var = self._new_tmp("unpack")
                    assign.append(f"{tmp_var} := {value}")

                    for i, elt in enumerate(target.elts):
                        if i < starred_idx:
                            idx_val = f"{tmp_var}[{i}]"
                            target_elt = elt
                        elif i == starred_idx:
                            # *b
                            start = i
                            end = len(target.elts) - 1 - i
                            if end > 0:
                                idx_val = f"{tmp_var}[{start}..{tmp_var}.len - {end}]"
                            else:
                                idx_val = f"{tmp_var}[{start}..]"
                            target_elt = elt.value
                        else:
                            # c
                            dist_from_end = len(target.elts) - 1 - i
                            if dist_from_end == 0:
                                idx_val = f"{tmp_var}.last()"
                            else:
                                idx_val = (
                                    f"{tmp_var}[{tmp_var}.len - {dist_from_end + 1}]"
                                )
                            target_elt = elt

                        subkw = ""
                        subop = ":="
                        if hasattr(node, "scopes"):
                            subkw = (
                                "mut "
                                if is_mutable(node.scopes, get_id(target_elt))
                                else ""
                            )
                            definition = node.scopes.parent_scopes.find(
                                get_id(target_elt)
                            ) or node.scopes.find(get_id(target_elt))
                            if definition is not None and defined_before(
                                definition, target_elt
                            ):
                                subop = "="

                        assign.append(
                            f"{subkw}{self.visit(target_elt)} {subop} {idx_val}"
                        )
                    continue

                value = value[1:-1]
                subtargets: List[str] = []
                op: str = ":="
                for subtarget in target.elts:
                    if hasattr(node, "scopes"):
                        subkw: str = (
                            "mut " if is_mutable(node.scopes, get_id(subtarget)) else ""
                        )
                        definition: Optional[py_ast.AST] = (
                            node.scopes.parent_scopes.find(get_id(subtarget))
                            or node.scopes.find(get_id(subtarget))
                        )
                    else:
                        subkw: str = "mut "
                        definition: Optional[py_ast.AST] = None
                    subtargets.append(f"{subkw}{self.visit(subtarget)}")
                    if definition is not None and defined_before(definition, subtarget):
                        op = "="
                    elif op == "=":
                        # Allow mixing if we already decided it's an assignment?
                        # Actually the original code raises here.
                        pass
                assign.append(f"{', '.join(subtargets)} {op} {value}")
            elif isinstance(target, (py_ast.Subscript, py_ast.Attribute)):
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            elif isinstance(target, py_ast.Name) and defined_before(
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

    def visit_AugAssign(self, node: py_ast.AugAssign) -> str:
        target: str = self.visit(node.target)
        op: str = self.visit(node.op)
        val: str = self.visit(node.value)
        return f"{target} {op}= {val}"

    def visit_Delete(self, node: py_ast.Delete) -> str:
        targets = []
        for target in node.targets:
            if isinstance(target, py_ast.Subscript):
                value = self.visit(target.value)
                slice = self.visit(target.slice)
                targets.append(f"{value}.delete({slice})")
            else:
                targets.append(f"/* del {self.visit(target)} */")
        return "\n".join(targets)

    def visit_Raise(self, node: py_ast.Raise) -> str:
        self._usings.add("div72.vexc")
        name = f'"{get_id(node.exc)}"'
        msg = '""'
        if node.exc is None:
            return "vexc.raise('Exception', '')"
        elif isinstance(node.exc, py_ast.Call):
            name = f'"{get_id(node.exc.func)}"'
            if node.exc.args:
                msg = self.visit(node.exc.args[0])
        return f"vexc.raise({name}, {msg})"

    def visit_With(self, node: py_ast.With) -> str:
        # V doesn't have 'with' statement, but we can use blocks and defer for cleanup
        # V's defer is block-scoped, which matches Python's context manager timing
        buf = ["{"]

        # Process items
        for i, item in enumerate(node.items):
            context = self.visit(item.context_expr)
            if "os.open" in context or "os.create" in context:
                if item.optional_vars:
                    target = self.visit(item.optional_vars)
                    buf.append(self.indent(f"mut {target} := {context}"))
                    buf.append(self.indent(f"defer {{ {target}.close() }}"))
                else:
                    tmp = self._new_tmp("file")
                    buf.append(self.indent(f"mut {tmp} := {context}"))
                    buf.append(self.indent(f"defer {{ {tmp}.close() }}"))
                continue

            # General context manager
            ctx_var = self._new_tmp("ctx")
            buf.append(self.indent(f"mut {ctx_var} := {context}"))
            buf.append(self.indent(f"defer {{ {ctx_var}.__exit__(0, 0, 0) }}"))

            if item.optional_vars:
                target = self.visit(item.optional_vars)
                buf.append(self.indent(f"mut {target} := {ctx_var}.__enter__()"))
            else:
                buf.append(self.indent(f"{ctx_var}.__enter__()"))

        # Process body
        for stmt in node.body:
            buf.append(self.indent(self.visit(stmt)))

        buf.append("}")
        return "\n".join(buf)

    def visit_Await(self, node: py_ast.Await) -> str:
        raise AstNotImplementedError("asyncio is not supported.", node)

    def visit_AsyncFunctionDef(self, node: py_ast.AsyncFunctionDef) -> str:
        # V doesn't have async/await, but we can convert async functions to regular ones
        # with warnings about lost async semantics
        # The function body will be processed normally, but async operations will be converted
        import warnings

        warnings.warn(
            f"Async function '{node.name}' converted to sync. Async semantics lost."
        )

        # Convert AsyncFunctionDef to FunctionDef for processing
        # Both have the same structure except the type
        func_node = py_ast.FunctionDef(
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

    def visit_Yield(self, node: py_ast.Yield) -> str:
        # V doesn't have generators, so we use channels
        # The function should be converted to accept a channel parameter
        # yield value becomes: ch <- value
        if node.value:
            return f"ch <- {self.visit(node.value)}"
        return "ch <- 0"  # Empty yield

    def visit_DictComp(self, node: py_ast.DictComp) -> str:
        if not node.generators:
            return "{}"

        # V does not support expression blocks, so represent dict comprehensions
        # as an immediately invoked function expression returning a `map[...]...`.
        key_type = get_inferred_v_type(node.key)
        if not key_type or key_type == "Any":
            # Try to infer `int` keys from `for x in range(...)` when the key is the loop var.
            if isinstance(node.key, py_ast.Name):
                for comp in node.generators:
                    if (
                        isinstance(comp.target, py_ast.Name)
                        and comp.target.id == node.key.id
                        and isinstance(comp.iter, py_ast.Call)
                        and get_id(comp.iter.func) == "range"
                    ):
                        key_type = "int"
                        break

        # V restricts map keys to basic types.
        if not key_type or key_type == "Any":
            key_type = "string"

        value_type = get_inferred_v_type(node.value) or "Any"

        buf: List[str] = []
        buf.append(f"(fn () map[{key_type}]{value_type} {{")
        buf.append(f"mut result := map[{key_type}]{value_type}{{}}")

        for comp in node.generators:
            target = comp.target
            iter_expr = comp.iter

            if isinstance(target, py_ast.Name):
                buf.append(f"for {target.id} in {self.visit(iter_expr)} {{")
            else:
                buf.append(f"for {self.visit(target)} in {self.visit(iter_expr)} {{")

            for if_clause in comp.ifs:
                buf.append(f"if {self.visit(if_clause)} {{")

            key = self.visit(node.key)
            value = self.visit(node.value)
            buf.append(f"result[{key}] = {value}")

            for _ in comp.ifs:
                buf.append("}")

            buf.append("}")

        buf.append("return result")
        buf.append("}())")
        return "\n".join(buf)

    def visit_GeneratorExp(self, node: py_ast.GeneratorExp) -> str:
        # V doesn't have generators, so we'll use an array
        # This should be handled by VComprehensionRewriter, but if not:
        if not node.generators:
            raise AstNotImplementedError("GeneratorExp with no generators", node)

        buf = []
        buf.append("mut result = []")

        for comp in node.generators:
            target = comp.target
            iter_expr = comp.iter

            if isinstance(target, py_ast.Name):
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

    def visit_ListComp(self, node: py_ast.ListComp) -> str:
        return self.visit_GeneratorExp(node)  # right now they are the same

    def visit_SetComp(self, node: py_ast.SetComp) -> str:
        # V doesn't have sets, so set comprehensions return arrays
        # The VComprehensionRewriter should handle this before it reaches here
        # If it reaches here, it means the rewriter didn't process it
        # So we fall back to the same logic as ListComp
        return self.visit_GeneratorExp(node)

    def visit_Global(self, node: py_ast.Global) -> str:
        # V doesn't have global keyword, but module-level variables are accessible
        # We'll just comment it out
        names = ", ".join(node.names)
        return f"// global {names}  // V doesn't support global keyword"

    def visit_IfExp(self, node: py_ast.IfExp) -> str:
        body: str = self.visit(node.body)
        orelse: str = self.visit(node.orelse)
        test: str = self.visit(node.test)
        return f"if {test} {{ {body} }} else {{ {orelse} }}"

    def visit_NamedExpr(self, node: py_ast.NamedExpr) -> str:
        # V doesn't support walrus operator, and it should be lifted by VWalrusRewriter
        # If we reach here, it means lifting failed or the node is in an unsupported context
        target = self.visit(node.target)
        value = self.visit(node.value)
        return f"({target} := {value})"

    def visit_AsyncFor(self, node: py_ast.AsyncFor) -> str:
        # V doesn't support async/await, so we'll convert to a synchronous loop.
        # The iterator may still be a channel-based generator.
        buf = ["// WARNING: async for converted to sync for"]

        for_node = py_ast.For(
            target=node.target,
            iter=node.iter,
            body=node.body,
            orelse=getattr(node, "orelse", []),
        )
        if hasattr(node, "scopes"):
            for_node.scopes = node.scopes
        for_node.level = getattr(node, "level", 0)

        buf.append(self.visit_For(for_node))
        return "\n".join(buf)

    def visit_AsyncWith(self, node: py_ast.AsyncWith) -> str:
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

    def visit_YieldFrom(self, node: py_ast.YieldFrom) -> str:
        # V doesn't have yield from, but we can iterate over another generator
        # yield from generator becomes:
        # for val in generator {
        #     ch <- val
        # }

        gen_expr = self.visit(node.value)
        gen_var = self._new_tmp("gen")

        buf: List[str] = []
        buf.append(f"{gen_var} := {gen_expr}")
        buf.append(f"// yield from {gen_var}")
        buf.append("for {")
        buf.append(f"    val := <-{gen_var} or {{ break }}")
        buf.append("    ch <- val")
        buf.append("}")

        return "\n".join(buf)
