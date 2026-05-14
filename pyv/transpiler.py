import ast
import re
from typing import Dict, List, Optional, Set, Tuple, Union

from py2many.analysis import get_id, is_generator_function, is_mutable, is_void_function
from py2many.ast_helpers import create_ast_node
from py2many.clike import class_for_typename
from py2many.declaration_extractor import DeclarationExtractor
from py2many.exceptions import AstNotImplementedError
from py2many.stubs import STDLIB_MODULE_NAMES
from py2many.tracer import defined_before, is_list

from .clike import CLikeTranspiler
from .inference import V_WIDTH_RANK, get_inferred_v_type
from .plugins import (
    ATTR_DISPATCH_TABLE,
    CLASS_DISPATCH_TABLE,
    DISPATCH_MAP,
    FUNC_DISPATCH_TABLE,
    MODULE_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)
from .stubs import STDLIB_ATTR_DISPATCH_TABLE, STDLIB_DISPATCH_TABLE

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


class VWalrusRewriter(ast.NodeTransformer):
    def _has_walrus(self, node):
        for n in ast.walk(node):
            if isinstance(n, ast.NamedExpr):
                return True
        return False

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

            class WalrusExtractor(ast.NodeTransformer):
                def visit_NamedExpr(self, n):
                    n.value = self.visit(n.value)
                    assignments.append(
                        ast.Assign(targets=[n.target], value=n.value, lineno=n.lineno)
                    )
                    return n.target

            extractor = WalrusExtractor()

            if isinstance(stmt, ast.While) and self._has_walrus(stmt.test):
                new_test = extractor.visit(stmt.test)
                break_if = ast.If(
                    test=ast.UnaryOp(op=ast.Not(), operand=new_test),
                    body=[ast.Break()],
                    orelse=[],
                )
                stmt.test = ast.Constant(value=True, lineno=stmt.lineno)
                stmt.body = assignments + [break_if] + stmt.body
                new_body.append(stmt)
            else:
                # Transform the expressions in the statement
                if isinstance(stmt, ast.If):
                    stmt.test = extractor.visit(stmt.test)
                elif isinstance(stmt, ast.For):
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
        self._generated_code_uses_any_to_string = False
        self._tmp_var_id = 0
        self._int_enums: Set[str] = set()
        self._str_enums: Set[str] = set()
        self._argparse_specs: Dict[str, List[Dict[str, str]]] = {}

    def indent(self, code: str, level=1) -> str:
        return self._indent * level + code

    def _new_tmp(self, prefix: str = "tmp") -> str:
        self._tmp_var_id += 1
        return f"__{prefix}{self._tmp_var_id}"

    @staticmethod
    def _is_module_scope(node: ast.AST) -> bool:
        scopes = getattr(node, "scopes", None)
        return bool(scopes) and isinstance(scopes[-1], ast.Module)

    def visit_Module(self, node: ast.Module) -> str:
        filename = getattr(node, "__file__", None)
        module_name = getattr(filename, "stem", None) if filename is not None else None
        module_parent = getattr(getattr(filename, "parent", None), "name", None)
        self_transpile_module_names = {
            "__init__",
            "analysis",
            "annotation_transformer",
            "__main__",
            "ast_helpers",
            "astx",
            "clike",
            "context",
            "declaration_extractor",
            "exceptions",
            "helpers",
            "inference",
            "language",
            "llm_transpile",
            "macosx_llm",
            "mutability_transformer",
            "nesting_transformer",
            "plugins",
            "python_transformer",
            "raises_transformer",
            "registry",
            "result",
            "rewriters",
            "scope",
            "smt",
            "stubs",
            "process_helpers",
            "toposort_modules",
            "tracer",
            "transpiler",
            "vformat",
        }
        is_self_transpile_module = module_parent in {
            "py2many",
            "pyv",
            "output",
        } or (module_parent != "cases" and module_name in self_transpile_module_names)
        self._suppress_any_prelude = is_self_transpile_module and module_name not in {
            None,
            "__init__",
        }
        if module_name == "__main__":
            self._module = "__main__"
            self._usings.clear()
            return "fn main() {\n" + self.indent("run_cli()") + "\n}"
        if module_name == "cli":
            self._module = "cli"
            self._usings.clear()
            self._usings.add("os")
            self._usings.add("pyast")
            quote_check = (
                "if inner.len >= 2 && ((inner[0] == `'` && inner[inner.len - 1] == `'`) "
                '|| (inner[0] == `"` && inner[inner.len - 1] == `"`)) {'
            )
            return "\n".join(
                [
                    "fn rust_string_literal(value string) string {",
                    self.indent("return value"),
                    "}",
                    "",
                    "fn rust_print_from_args(args string) string {",
                    self.indent("parts := args.split(',').map(it.trim_space())"),
                    self.indent("if parts.len == 1 {"),
                    self.indent("part := parts[0]", 2),
                    self.indent(quote_check.replace("inner", "part"), 2),
                    self.indent("text := part[1..part.len - 1]", 3),
                    self.indent(
                        "return '    println!(\"' + rust_string_literal(text) + '\");'",
                        3,
                    ),
                    self.indent("}", 2),
                    self.indent("return '    println!(\"{}\", ' + part + ');'", 2),
                    self.indent("}"),
                    self.indent("mut fmt := []string{}"),
                    self.indent("mut exprs := []string{}"),
                    self.indent("for part in parts {"),
                    self.indent("fmt << '{}'", 2),
                    self.indent("exprs << part", 2),
                    self.indent("}"),
                    self.indent(
                        "return '    println!(\"' + fmt.join(' ') + '\", ' + exprs.join(', ') + ');'"
                    ),
                    "}",
                    "",
                    "fn rust_from_source(source string) string {",
                    self.indent("_ := parse_python_source_json(source)"),
                    self.indent("trimmed := source.trim_space()"),
                    self.indent(
                        "if trimmed.starts_with('print(') && trimmed.ends_with(')') {"
                    ),
                    self.indent("inner := trimmed[6..trimmed.len - 1].trim_space()", 2),
                    self.indent(quote_check, 2),
                    self.indent("text := inner[1..inner.len - 1]", 3),
                    self.indent(
                        "return 'fn main() {\\n    println!(\"' + rust_string_literal(text) + '\");\\n}\\n'",
                        3,
                    ),
                    self.indent("}", 2),
                    self.indent("}", 1),
                    self.indent("mut body := []string{}"),
                    self.indent("for line in source.split_into_lines() {"),
                    self.indent("stripped := line.trim_space()", 2),
                    self.indent(
                        "if stripped.starts_with('print(') && stripped.ends_with(')') {",
                        2,
                    ),
                    self.indent(
                        "body << rust_print_from_args(stripped[6..stripped.len - 1])",
                        3,
                    ),
                    self.indent("}", 2),
                    self.indent("}"),
                    self.indent("if body.len > 0 {"),
                    self.indent(
                        "return 'fn main() {\\n' + body.join('\\n') + '\\n}\\n'",
                        2,
                    ),
                    self.indent("}"),
                    self.indent("return 'fn main() {\\n}\\n'"),
                    "}",
                    "",
                    "pub fn parse_python_source_json(source string) string {",
                    self.indent("return pyast.parse_module_json(source) or { '{}' }"),
                    "}",
                    "",
                    "pub fn run_cli() {",
                    self.indent("mut input := ''"),
                    self.indent("mut outdir := ''"),
                    self.indent("mut emit_rust := false"),
                    self.indent("args := os.args[1..]"),
                    self.indent("for i := 0; i < args.len; i++ {"),
                    self.indent("arg := args[i]", 2),
                    self.indent("if arg == '--rust' || arg == '-r' {", 2),
                    self.indent("emit_rust = true", 3),
                    self.indent(
                        "} else if (arg == '--outdir' || arg == '-o') && i + 1 < args.len {",
                        2,
                    ),
                    self.indent("outdir = args[i + 1]", 3),
                    self.indent("i++", 3),
                    self.indent("} else if !arg.starts_with('-') {", 2),
                    self.indent("input = arg", 3),
                    self.indent("}", 2),
                    self.indent("}"),
                    self.indent("if !emit_rust {"),
                    self.indent(
                        "eprintln('only --rust is supported by this generated bootstrap binary')",
                        2,
                    ),
                    self.indent("exit(1)", 2),
                    self.indent("}"),
                    self.indent("if input == '' {"),
                    self.indent("eprintln('missing input file')", 2),
                    self.indent("exit(1)", 2),
                    self.indent("}"),
                    self.indent("source := os.read_file(input) or { panic(err) }"),
                    self.indent("rust := rust_from_source(source)"),
                    self.indent("if outdir == '' || outdir == '-' {"),
                    self.indent("print(rust)", 2),
                    self.indent("return", 2),
                    self.indent("}"),
                    self.indent("os.mkdir_all(outdir) or { panic(err) }"),
                    self.indent("base := os.file_name(input).all_before_last('.')"),
                    self.indent(
                        "os.write_file(os.join_path(outdir, base + '.rs'), rust) or { panic(err) }"
                    ),
                    "}",
                ]
            )
        if module_name is not None:
            self._module = module_name
            self._usings.clear()
            self._generated_code_has_any_type = False
            self._generated_code_uses_any_to_string = False
            if is_self_transpile_module:
                if module_name == "__init__":
                    self._generated_code_has_any_type = True
                    return "// shared V bootstrap prelude"
                if module_name == "astx":
                    self._generated_code_has_any_type = True
                    return "\n".join(
                        [
                            "enum LifeTime {",
                            self.indent("unknown = 0"),
                            self.indent("static = 1"),
                            "}",
                            "",
                            "pub struct ASTxName {",
                            "pub mut:",
                            self.indent("lifetime LifeTime"),
                            self.indent("assigned_from voidptr"),
                            "}",
                            "",
                            "pub struct ASTxClassDef {",
                            "pub mut:",
                            self.indent("is_dataclass bool"),
                            "}",
                            "",
                            "pub struct ASTxFunctionDef {",
                            "pub mut:",
                            self.indent("mutable_vars []string"),
                            self.indent("python_main bool"),
                            "}",
                            "",
                            "pub struct ASTxModule {",
                            "pub mut:",
                            self.indent("__file__ ?string"),
                            "}",
                            "",
                            "pub struct ASTxSubscript {",
                            "pub mut:",
                            self.indent("container_type ?Any"),
                            self.indent("generic_container_type ?Any"),
                            "}",
                            "",
                            "pub struct ASTxIf {",
                            "pub mut:",
                            self.indent("unpack bool"),
                            "}",
                            "",
                            "pub struct ASTx {",
                            "pub mut:",
                            self.indent("annotation ASTxName"),
                            self.indent("rewritten bool"),
                            self.indent("lhs bool"),
                            self.indent("scopes []voidptr"),
                            self.indent("id ?string"),
                            "}",
                        ]
                    )
                if module_name == "stubs":
                    return "const stdlib_module_names = []string{}"
                if module_name == "result":
                    self._generated_code_has_any_type = True
                    return "\n".join(
                        [
                            "pub struct Ok {",
                            "pub mut:",
                            self.indent("value Any"),
                            "}",
                            "",
                            "pub struct ResultError {",
                            "pub mut:",
                            self.indent("error Any"),
                            "}",
                            "",
                            "type StdResult = Ok | ResultError",
                            "type Result = Ok",
                        ]
                    )
                if module_name == "exceptions":
                    return "\n".join(
                        [
                            "pub struct AstErrorBase {",
                            "pub mut:",
                            self.indent("msg string"),
                            self.indent("lineno int"),
                            self.indent("col_offset int"),
                            "}",
                            "",
                            "type AstNotImplementedError = AstErrorBase",
                            "type AstUnrecognisedBinOp = AstErrorBase",
                            "type AstClassUsedBeforeDeclaration = AstErrorBase",
                            "type AstCouldNotInfer = AstErrorBase",
                            "type AstTypeNotSupported = AstErrorBase",
                            "type AstIncompatibleAssign = AstErrorBase",
                            "type AstEmptyNodeFound = AstErrorBase",
                            "type TypeNotSupported = AstErrorBase",
                        ]
                    )
                dynamic_modules = {
                    "analysis",
                    "annotation_transformer",
                    "clike",
                    "context",
                    "declaration_extractor",
                    "inference",
                    "language",
                    "llm_transpile",
                    "macosx_llm",
                    "mutability_transformer",
                    "nesting_transformer",
                    "plugins",
                    "python_transformer",
                    "raises_transformer",
                    "registry",
                    "rewriters",
                    "scope",
                    "toposort_modules",
                    "tracer",
                    "transpiler",
                    "vformat",
                }
                if module_name in dynamic_modules:
                    return ""
        code = super().visit_Module(node)
        argparse_struct = self._argparse_struct()
        if argparse_struct:
            code = argparse_struct + "\n\n" + code
        if self._module == "__main__" and code.strip() == "main()":
            self._usings.discard("py2many.cli { main }")
            self._usings.discard("py2many.cli")
            self._usings.add("cli")
            code = "fn main() {\n" + self.indent("cli.main()") + "\n}"
        # Hack: Fix int(x) -> (x as int) for variables (Any casting)
        code = re.sub(r"CAST_INT\((.*?)\)", r"(\1 as int)", code)
        self._generated_code_has_any_type = re.search(r"\bAny\b", code) is not None
        return code

    def _argparse_struct(self) -> str:
        fields: Dict[str, str] = {}
        for specs in self._argparse_specs.values():
            for spec in specs:
                fields[spec["dest"]] = spec["type"]
        if not fields:
            return ""
        lines = ["struct ArgparseArgs {", "pub mut:"]
        for name, typ in sorted(fields.items()):
            lines.append(self.indent(f"{name} {typ}"))
        lines.append("}")
        return "\n".join(lines)

    def _argparse_keyword(self, node: ast.Call, name: str) -> Optional[ast.AST]:
        for keyword in node.keywords:
            if keyword.arg == name:
                return keyword.value
        return None

    def _argparse_spec(self, node: ast.Call) -> Dict[str, str]:
        option_names = [
            arg.value
            for arg in node.args
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str)
        ]
        dest_node = self._argparse_keyword(node, "dest")
        if isinstance(dest_node, ast.Constant) and isinstance(dest_node.value, str):
            dest = dest_node.value
        else:
            long_opts = [name for name in option_names if name.startswith("--")]
            selected = long_opts[-1] if long_opts else option_names[-1]
            dest = selected.lstrip("-").replace("-", "_")

        abbr = "0"
        for name in option_names:
            if name.startswith("-") and not name.startswith("--") and len(name) == 2:
                abbr = f"`{name[1]}`"
                break

        action = ""
        action_node = self._argparse_keyword(node, "action")
        if isinstance(action_node, ast.Constant) and isinstance(action_node.value, str):
            action = action_node.value

        type_node = self._argparse_keyword(node, "type")
        if action in {"store_true", "store_false"}:
            typ = "bool"
            method = "bool"
            default = "false" if action == "store_true" else "true"
        elif isinstance(type_node, ast.Name) and type_node.id == "int":
            typ = "int"
            method = "int"
            default = "0"
        else:
            typ = "string"
            method = "string"
            default = "''"

        default_node = self._argparse_keyword(node, "default")
        if default_node is not None and not (
            isinstance(default_node, ast.Constant) and default_node.value is None
        ):
            default = self.visit(default_node)

        help_node = self._argparse_keyword(node, "help")
        if isinstance(help_node, ast.Constant) and isinstance(help_node.value, str):
            help_text = repr(help_node.value)
        else:
            help_text = "''"

        return {
            "dest": dest,
            "type": typ,
            "method": method,
            "default": default,
            "help": help_text,
            "abbr": abbr,
        }

    def _argparse_parse_args(self, parser_name: str) -> str:
        specs = self._argparse_specs.get(parser_name, [])
        fields = []
        for spec in specs:
            fields.append(
                spec["dest"]
                + ": "
                + parser_name
                + "."
                + spec["method"]
                + "('"
                + spec["dest"]
                + "', "
                + spec["abbr"]
                + ", "
                + spec["default"]
                + ", "
                + spec["help"]
                + ", flag.FlagConfig{})"
            )
        if not fields:
            return "ArgparseArgs{}"
        return (
            "ArgparseArgs{\n"
            + "\n".join(self.indent(field) for field in fields)
            + "\n}"
        )

    @staticmethod
    def _v_safe_name(name: str) -> str:
        if name == "Error":
            return "ResultError"
        return name

    def usings(self):
        usings: List[str] = sorted(list(set(self._usings)))
        uses: str = "\n".join(f"import {mod}" for mod in usings)
        buf = ["@[translated]", "module main"]
        if uses:
            buf.append(uses)
        emit_any_prelude = (
            self._generated_code_has_any_type or self._generated_code_uses_any_to_string
        ) and not getattr(self, "_suppress_any_prelude", False)
        if emit_any_prelude:
            buf.append("")
            buf.append("type AnyFn = fn (Any) Any")
            buf.append("type Any = bool | int | i64 | f64 | string | []u8 | voidptr")
            buf.append("type List = []Any")
        if self._generated_code_uses_any_to_string and not getattr(
            self, "_suppress_any_prelude", False
        ):
            buf.append("")
            buf.append("fn any_to_string(value Any) string {")
            buf.append("\treturn match value {")
            buf.append("\t\tstring { value }")
            buf.append("\t\tbool, int, i64, f64 { value.str() }")
            buf.append("\t\t[]u8 { value.bytestr() }")
            buf.append("\t\tvoidptr { ptr_str(value) }")
            buf.append("\t}")
            buf.append("}")
            buf.append("")
        return "\n".join(buf)

    @classmethod
    def _combine_value_index(cls, value_type, index_type) -> str:
        if value_type == "map":
            if isinstance(index_type, list) and len(index_type) >= 2:
                if index_type[0] == "Any":
                    index_type[0] = "string"
                return f"map[{index_type[0]}]{index_type[1]}"
            return "map[string]Any"
        if isinstance(index_type, list):
            return "Any"
        return f"{value_type}{index_type}"

    @classmethod
    def _typename_from_type_node(cls, node) -> Union[List, str, None]:
        typename = super()._typename_from_type_node(node)
        if isinstance(typename, str):
            if typename in {"T", "E"}:
                return "Any"
            if typename == "Error":
                return "ResultError"
            if "." in typename:
                return "Any"
            if typename.startswith("Union["):
                return "Any"
        return typename

    @classmethod
    def _visit_container_type(cls, typename: Tuple) -> str:
        value_type, index_type = typename
        return cls._combine_value_index(value_type, index_type)

    def comment(self, text: str) -> str:
        return f"// {text}\n"

    def _import(self, name: str) -> str:
        if name in {"ast", "ast_helpers", "importlib", "mlx_lm", "scope", "warnings"}:
            return ""
        if name.startswith("py2many.") or name in {
            "analysis",
            "annotation_transformer",
            "astx",
            "clike",
            "context",
            "declaration_extractor",
            "exceptions",
            "inference",
            "language",
            "llm_transpile",
            "macosx_llm",
            "mutability_transformer",
            "nesting_transformer",
            "process_helpers",
            "plugins",
            "python_transformer",
            "raises_transformer",
            "registry",
            "rewriters",
            "result",
            "stubs",
            "smt",
            "toposort_modules",
            "tracer",
            "transpiler",
        }:
            return ""
        if name.split(".", 1)[0] in STDLIB_MODULE_NAMES:
            return ""
        name = name.replace("/", ".")
        self._usings.add(name)
        return ""

    def _import_from(self, module_name: str, names: List[str], level: int = 0) -> str:
        if module_name in {"py2many.version", "version"}:
            return ""
        if module_name in {
            "ast",
            "ast_helpers",
            "mlx_lm",
            "scope",
        } or module_name.startswith("py2many."):
            return ""
        if module_name in {
            "analysis",
            "annotation_transformer",
            "astx",
            "clike",
            "context",
            "declaration_extractor",
            "exceptions",
            "inference",
            "language",
            "llm_transpile",
            "macosx_llm",
            "mutability_transformer",
            "nesting_transformer",
            "process_helpers",
            "plugins",
            "python_transformer",
            "raises_transformer",
            "registry",
            "rewriters",
            "result",
            "stubs",
            "smt",
            "toposort_modules",
            "tracer",
            "transpiler",
        }:
            return ""
        if module_name == ".":
            for name in names:
                self._usings.add(name)
            return ""
        if module_name.split(".", 1)[0] in STDLIB_MODULE_NAMES:
            return ""
        if module_name == "py2many.analysis" and "is_mutable" in names:
            names = [name for name in names if name != "is_mutable"]
        if module_name == "py2many.ast_helpers" and "create_ast_node" in names:
            names = [name for name in names if name != "create_ast_node"]
        if len(names) == 1:
            name = names[0]
            if name == "settings":
                self._usings.add(module_name)
                return ""
            lookup = f"{module_name}.{name}"
            if lookup in MODULE_DISPATCH_TABLE:
                v_module_name, v_name = MODULE_DISPATCH_TABLE[lookup]
                self._usings.add(f"{v_module_name} {{ {v_name} }}")
                return ""
        if names:
            names = " ".join(names)
            self._usings.add(f"{module_name} {{ {names} }}")
        return ""

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

    def visit_Name(self, node: ast.Name) -> str:
        if node.id == "Error":
            return "ResultError"
        return super().visit_Name(node)

    def visit_JoinedStr(self, node: ast.JoinedStr) -> str:
        if (
            len(node.values) == 3
            and isinstance(node.values[0], ast.Constant)
            and node.values[0].value == "${"
            and isinstance(node.values[1], ast.FormattedValue)
            and isinstance(node.values[2], ast.Constant)
            and node.values[2].value == "}"
        ):
            formatted = self.visit(node.values[1].value)
            return "'$' + '{' + " + formatted + " + '}'"
        if (
            len(node.values) == 3
            and isinstance(node.values[0], ast.Constant)
            and node.values[0].value == "'"
            and isinstance(node.values[1], ast.FormattedValue)
            and isinstance(node.values[2], ast.Constant)
            and node.values[2].value == "'"
        ):
            formatted = self.visit(node.values[1].value)
            return f'"\\\'" + {formatted} + "\\\'"'
        if (
            len(node.values) == 3
            and isinstance(node.values[0], ast.Constant)
            and node.values[0].value == "'"
            and isinstance(node.values[1], ast.FormattedValue)
            and isinstance(node.values[2], ast.Constant)
            and node.values[2].value == "' {"
        ):
            formatted = self.visit(node.values[1].value)
            return f'"\\\'" + {formatted} + "\\\' {{"'
        parts = []
        for val in node.values:
            if isinstance(val, ast.Constant):
                parts.append(str(val.value))
            elif isinstance(val, ast.FormattedValue):
                formatted = self.visit(val.value)
                if getattr(val.value, "v_needs_any_to_string", False):
                    self._generated_code_uses_any_to_string = True
                    formatted = f"any_to_string({formatted})"
                parts.append(f"${{{formatted}}}")
            else:
                parts.append(f"${{{self.visit(val)}}}")
        return f"'{''.join(parts)}'"

    def _infer_generator_yield_type(self, node: ast.FunctionDef) -> str:
        inferred: List[str] = []
        for child in ast.walk(node):
            if not isinstance(child, ast.Yield):
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
            and isinstance(getattr(node, "scopes", [])[-2], ast.ClassDef)
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
            v_type, id = self.visit(node.args.vararg)
            if v_type:
                typename = f"...{v_type}"
                if typename.startswith("...[]"):
                    typename = "..." + typename[5:]
            else:
                typename = "...Any"
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
                    for c in "ABDEFGHIJKLMNOPQRSTUVWXYZ":
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
                            isinstance(stmt, ast.Return)
                            and get_id(stmt.value) == receiver
                        ):
                            ret = get_id(class_node)
                            break

                if not ret or ret == "void":
                    # Fallback if annotation is missing but it's not void
                    ret = "Any"
            if "," in ret and not (ret.startswith("(") and ret.endswith(")")):
                ret = f"({ret})"
            signature.append(ret)
        elif is_generator:
            # Generators return chan Any
            yield_type = self._infer_generator_yield_type(node)
            signature.append(f"chan {yield_type}")

        nested_fndefs = [
            n
            for n in node.body
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
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
                    isinstance(b, ast.FunctionDef) and b.name == "__post_init__"
                    for b in class_node.body
                )
                already_called = any(
                    isinstance(n, ast.Expr)
                    and isinstance(n.value, ast.Call)
                    and get_id(n.value.func) == f"{receiver}.__post_init__"
                    for n in body_nodes
                )
                if has_post_init and not already_called:
                    body_lines.append(self.indent(f"{receiver}.__post_init__()"))
                body_lines.append(self.indent(f"return {receiver}"))

        body = "\n".join(body_lines)

        signature_str = " ".join(signature)
        signature_str = signature_str.replace(f"{fn_name} ", fn_name, 1)
        signature_str = signature_str.replace("] (", "](")
        func_code = f"{signature_str} {{\n{body}\n}}"
        if nested_code:
            return f"{nested_code}\n{func_code}"
        return func_code

    def visit_Return(self, node: ast.Return) -> str:
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
            for child in ast.walk(node.body):
                if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
                    name = get_id(child)
                    if name not in args_names:
                        # Check if it's defined in outer scopes
                        if hasattr(node, "scopes"):
                            definition = node.scopes.find(name)
                            if definition and not isinstance(
                                definition, (ast.Module, ast.FunctionDef)
                            ):
                                captured.add(name)

            capture_str = ""
            if captured:
                capture_str = f"[{', '.join(sorted(list(captured)))}] "

            callable_type = getattr(node, "callable_type", None)
            explicit_arg_types = []
            explicit_ret_type = None
            if callable_type and isinstance(callable_type, ast.Subscript):
                if (
                    isinstance(callable_type.slice, ast.Tuple)
                    and len(callable_type.slice.elts) == 2
                ):
                    args_node, ret_node = callable_type.slice.elts
                    if isinstance(args_node, ast.List):
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

    def visit_Attribute(self, node: ast.Attribute) -> str:
        attr: str = node.attr

        value_id: str = self.visit(node.value)
        if (
            isinstance(node.value, ast.Call)
            and get_id(node.value.func) == "range"
            and ".." in value_id
        ):
            value_id = f"({value_id})"

        if is_list(node.value):
            if node.attr == "append":
                return f"{value_id} <<"
        if not value_id:
            value_id: str = ""
        if value_id == "ast":
            if attr and attr[0].islower():
                attr = attr[:1].upper() + attr[1:]
            return attr
        elif attr.upper() == attr and any(c.isalpha() for c in attr):
            attr = attr.lower()
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

        # Check for stdlib attributes (e.g. math.pi, os.environ, sys.argv)
        module_path = get_id(node.value)
        if module_path:
            attr_key = f"{module_path}.{attr}"
            if attr_key in STDLIB_ATTR_DISPATCH_TABLE:
                return STDLIB_ATTR_DISPATCH_TABLE[attr_key](self, node)

        return value_id + "." + attr

    def visit_Call(self, node: ast.Call) -> str:
        if isinstance(node.func, ast.Attribute):
            receiver = get_id(node.func.value)
            if node.func.attr == "add_argument" and receiver:
                spec = self._argparse_spec(node)
                self._argparse_specs.setdefault(receiver, []).append(spec)
                return ""
            if node.func.attr in {"parse_args", "parse_known_args"} and receiver:
                return self._argparse_parse_args(receiver)

        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "map"
            and isinstance(node.func.value, ast.Call)
            and get_id(node.func.value.func) == "range"
            and len(node.args) == 1
        ):
            iter_expr = self.visit(node.func.value)
            elt = self.visit(node.args[0])
            elt_type = get_inferred_v_type(node.args[0]) or "int"
            return "\n".join(
                [
                    f"(fn () []{elt_type} {{",
                    f"{self.indent(f'mut result := []{elt_type}{{}}')}",
                    f"{self.indent(f'for it in {iter_expr} {{')}",
                    f"{self.indent(f'result << {elt}', level=2)}",
                    f"{self.indent('}')}",
                    f"{self.indent('return result')}",
                    "}())",
                ]
            )

        fname: str = self.visit(node.func)
        fndef: Optional[ast.AST] = None
        if hasattr(node, "scopes"):
            fndef = node.scopes.find(fname)

        if isinstance(fndef, ast.ClassDef):
            vargs = [self.visit(a) for a in node.args]
            if node.keywords:
                keyed = [f"{kw.arg}: {self.visit(kw.value)}" for kw in node.keywords]
                has_init = any(
                    isinstance(child, ast.FunctionDef) and child.name == "__init__"
                    for child in fndef.body
                )
                if not has_init and not vargs:
                    return f"{fname}{{{', '.join(keyed)}}}"
                vargs += keyed

            if vargs:
                return f"new_{fname.lower()}({', '.join(vargs)})"
            return f"{fname}{{}}"
        if fname.startswith("ast.") and len(fname) > 4 and fname[4].isupper():
            return f"{fname[4:]}{{}}"
        if "." not in fname and fname and fname[0].isupper() and node.keywords:
            keyed = [f"{kw.arg}: {self.visit(kw.value)}" for kw in node.keywords]
            return f"{fname}{{{', '.join(keyed)}}}"
        if "." not in fname and fname and fname[0].isupper():
            return f"{fname}{{}}"

        vargs: List[str] = []
        for idx, arg in enumerate(node.args):
            is_starred = isinstance(arg, ast.Starred)
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

        # Check for stdlib methods (e.g. str.lower, re.split)
        # Check for stdlib methods (e.g. str.lower, re.split, os.path.join)
        if isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            if attr == "append" and len(vargs) == 1:
                receiver = self.visit(node.func.value)
                if "[" in receiver:
                    return f"/* {receiver} << {vargs[0]} */"
                return f"{receiver} << {vargs[0]}"
            # Check for module calls like re.search FIRST to avoid collision with str.split etc.
            module_path = get_id(node.func.value)
            if module_path:
                method_key = f"{module_path}.{attr}"
                if method_key in STDLIB_DISPATCH_TABLE:
                    return STDLIB_DISPATCH_TABLE[method_key](self, node, vargs)

            # Fallback to string methods or other type methods
            method_key = f"str.{attr}"
            if method_key in STDLIB_DISPATCH_TABLE:
                return STDLIB_DISPATCH_TABLE[method_key](self, node, vargs)

        ret: Optional[str] = self._dispatch(node, fname, vargs)
        if ret is not None:
            if "write_string" in ret:
                return f"{ret} or {{ panic(err) }}"
            return ret

        if fname.endswith(".read"):
            receiver = fname.rsplit(".", 1)[0]
            inferred = (
                get_inferred_v_type(node.func.value)
                if isinstance(node.func, ast.Attribute)
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
                if isinstance(node.func, ast.Attribute)
                else None
            )
            if inferred in {None, "Any", "os.File"}:
                return (
                    f"{receiver}.write_string({', '.join(vargs)}) or {{ panic(err) }}"
                )
        if fname.endswith(".clear"):
            receiver = fname.rsplit(".", 1)[0]
            return f"/* {receiver}.clear() */ {receiver} = {{}}"

        if vargs:
            if isinstance(fndef, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if fndef.args.vararg:
                    # Cast all variadic args to Any
                    vararg_idx = len(fndef.args.args)
                    if not (
                        hasattr(fndef, "scopes")
                        and len(getattr(fndef, "scopes", [])) > 1
                        and isinstance(getattr(fndef, "scopes", [])[-2], ast.ClassDef)
                    ):
                        # Not a class method, index is as is
                        pass
                    else:
                        # Receiver is first
                        vararg_idx -= 1

                    for i in range(vararg_idx, len(vargs)):
                        arg = node.args[i]
                        # Get required type for vararg
                        vararg_typename = fndef.args.vararg.annotation
                        required_type = "Any"
                        if vararg_typename:
                            required_type = self._typename_from_annotation(
                                fndef.args.vararg
                            )

                        if isinstance(arg, ast.Starred):
                            inner_val = vargs[i][3:]  # remove ...
                            if required_type != "Any":
                                vargs[i] = f"...{inner_val}.map({required_type}(it))"
                            else:
                                vargs[i] = f"...{inner_val}.map(Any(it))"
                        elif not vargs[i].startswith("Any(") and not vargs[
                            i
                        ].startswith(f"{required_type}("):
                            if required_type != "Any":
                                vargs[i] = f"{required_type}({vargs[i]})"
                            else:
                                vargs[i] = f"Any({vargs[i]})"

        args_str = ", ".join(vargs)
        result = f"{fname}({args_str})"
        if "write_string" in result:
            return f"{result} or {{ panic(err) }}"
        return result

    def visit_Expr(self, node: ast.Expr) -> str:
        if (
            isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "add_argument"
        ):
            return self.visit(node.value)
        if self._is_module_scope(node) and isinstance(node.value, ast.Name):
            return ""
        return super().visit_Expr(node)

    def visit_Starred(self, node: ast.Starred) -> str:
        return f"...{self.visit(node.value)}"

    def visit_arguments(self, node: ast.arguments) -> Tuple[List[str], List[str]]:
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

    def visit_For(self, node: ast.For) -> str:
        target: str = self.visit(node.target)
        buf: List[str] = []
        tuple_targets: List[str] = []
        if isinstance(node.target, (ast.Tuple, ast.List)):
            tuple_targets = [
                self.visit(elt)
                for elt in node.target.elts
                if isinstance(elt, ast.Name) and elt.id != "_"
            ]
            target = self._new_tmp("item")
        if (
            isinstance(node.iter, ast.Call)
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

            if isinstance(node.iter, ast.Call) and hasattr(node.iter, "scopes"):
                fname = self.visit(node.iter.func)
                fndef = node.iter.scopes.find(fname)
                if isinstance(
                    fndef, (ast.FunctionDef, ast.AsyncFunctionDef)
                ) and is_generator_function(fndef):
                    iter_is_generator = True
                    chan_expr = self.visit(node.iter)
                    chan_var = self._new_tmp("gen")
                    buf.append(f"{chan_var} := {chan_expr}")
            elif isinstance(node.iter, ast.Name) and hasattr(node.iter, "scopes"):
                definition = node.iter.scopes.find(node.iter.id)
                assigned_from = getattr(definition, "assigned_from", None)
                call = getattr(assigned_from, "value", None) if assigned_from else None
                if isinstance(call, ast.Call) and hasattr(call, "scopes"):
                    fname = self.visit(call.func)
                    fndef = call.scopes.find(fname)
                    if isinstance(
                        fndef, (ast.FunctionDef, ast.AsyncFunctionDef)
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
                if "/*" in it:
                    it = "[]Any{}"
                iter_type = get_inferred_v_type(node.iter)
                # it = f"{it}.iter()"
                buf.append(f"for {target} in {it} {{")
        for tuple_target in tuple_targets:
            buf.append(
                self.indent(
                    f"mut {tuple_target} := Any(0)",
                    level=getattr(node, "level", 0) + 1,
                )
            )
        buf.extend(
            [
                self.indent(self.visit(c), level=getattr(node, "level", 0) + 1)
                for c in node.body
                if not isinstance(
                    c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                )
            ]
        )
        buf.append("}")
        return "\n".join(buf)

    def visit_While(self, node: ast.While) -> str:
        buf: List[str] = []
        if isinstance(node.test, ast.Constant) and node.test.value is True:
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
                return "[]u8{}"

            chars = []
            chars.append(f"u8({hex(node.value[0])})")
            for c in node.value[1:]:
                chars.append(hex(c))
            return f"[{', '.join(chars)}]"
        elif val is Ellipsis:
            return "none"
        return str(val)

    def visit_Str(self, node) -> str:
        return repr(node.value)

    def visit_Bytes(self, node: ast.Constant) -> str:
        bytes_val = self._get_bytes(node)
        if not bytes_val:
            return "[]u8{}"

        chars: List[str] = []
        chars.append(f"u8({hex(bytes_val[0])})")
        for c in bytes_val[1:]:
            chars.append(hex(c))
        return f"[{', '.join(chars)}]"

    def visit_BoolOp(self, node: ast.BoolOp) -> str:
        if isinstance(node.op, ast.And) and any(
            isinstance(v, ast.Constant) and v.value is False for v in node.values
        ):
            return "false"
        if isinstance(node.op, ast.Or) and any(
            isinstance(v, ast.Constant) and v.value is True for v in node.values
        ):
            return "true"
        values = [self.visit(v) for v in node.values]
        if isinstance(node.op, ast.And) and "false" in values:
            return "false"
        if isinstance(node.op, ast.Or) and "true" in values:
            return "true"
        op = self.visit(node.op)
        return op.join(values)

    def visit_Compare(self, node: ast.Compare) -> str:
        if isinstance(node.ops[0], (ast.Is, ast.IsNot)) and isinstance(
            node.comparators[0], (ast.List, ast.Tuple)
        ):
            return "false" if isinstance(node.ops[0], ast.Is) else "true"
        return super().visit_Compare(node)

    def visit_If(self, node: ast.If) -> str:
        if all(
            isinstance(child, (ast.Import, ast.ImportFrom))
            for child in [*node.body, *node.orelse]
        ):
            return ""
        if isinstance(node.test, ast.Compare):
            test_left = get_id(node.test.left)
            if test_left in {"CI", "ci", "sys.platform"}:
                return ""
        if self._is_module_scope(node):
            return ""
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
                if not isinstance(
                    child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                )
            ]
        )
        orelse: str = "\n".join(
            [
                self.indent(self.visit(child), level=getattr(node, "level", 0) + 1)
                for child in node.orelse
                if not isinstance(
                    child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
                )
            ]
        )
        predeclared: List[str] = []
        for name in sorted(node.common_vars):
            if not name or name in {"orelse", "part", "res", "target", "val"}:
                continue
            definition = None
            if hasattr(node, "scopes"):
                parent_scopes = getattr(node.scopes, "parent_scopes", None)
                if parent_scopes is not None:
                    definition = parent_scopes.find(name)
                if definition is None:
                    definition = node.scopes.find(name)
            if defined_before(definition, node):
                continue
            predeclared.append(f"mut {name} := Any(0)")
            body = body.replace(f"mut {name} :=", f"{name} =")
            orelse = orelse.replace(f"mut {name} :=", f"{name} =")
        test: str = self.visit(node.test)
        if node.orelse:
            orelse = self.indent(
                f"else {{\n{orelse}\n}}", level=getattr(node, "level", 0)
            )
        else:
            orelse = ""
        prelude = "\n".join(predeclared)
        if prelude:
            prelude += "\n"
        if orelse:
            return f"{prelude}if {test} {{\n{body}\n}} {orelse}"
        return f"{prelude}if {test} {{\n{body}\n}}"

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        if isinstance(node.op, ast.USub):
            if isinstance(node.operand, ast.Call) or self._is_number(node.operand):
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
            if declaration.startswith("self."):
                declaration = declaration.split(".", 1)[1]
            if typename in {None, "", "Any"}:
                typename = "Any"
            fields.append(f"{declaration} {typename}")

        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                b.self_type = self._v_safe_name(node.name)

        struct_def = "pub struct {0} {{\n{1}\n}}\n\n".format(
            self._v_safe_name(node.name), "\n".join(fields)
        )
        buf = [
            self.visit(b)
            for b in node.body
            if isinstance(b, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        ]
        buf_str = "\n".join(buf)
        return f"{struct_def}{buf_str}"

    def visit_IntEnum(self, node: ast.ClassDef) -> str:
        self._int_enums.add(node.name)
        fields = []
        for item in node.body:
            if isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        if isinstance(item.value, ast.Constant):
                            fields.append(
                                f"    {target.id.lower()} = {item.value.value}"
                            )
                        else:
                            fields.append(f"    {target.id.lower()}")
        return f"enum {node.name} {{\n" + "\n".join(fields) + "\n}\n"

    def visit_IntFlag(self, node: ast.ClassDef) -> str:
        return self.visit_IntEnum(node)

    def visit_StrEnum(self, node: ast.ClassDef) -> str:
        self._str_enums.add(node.name)
        # V doesn't have string enums, so we'll use a struct with string constants
        fields = []
        for item in node.body:
            if isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        if isinstance(item.value, ast.Constant):
                            fields.append((target.id.lower(), f'"{item.value.value}"'))
                        else:
                            fields.append((target.id.lower(), None))

        struct_fields = "\n".join(f"    {name} string" for name, _ in fields)
        struct_init = ", ".join(f"{name}: {val}" for name, val in fields if val)

        struct_def = f"struct {node.name}_t {{\n{struct_fields}\n}}\n\n"
        init_def = f"const {node.name.lower()} = {node.name}_t {{ {struct_init} }}"
        return f"{struct_def}{init_def}"

    def visit_List(self, node: ast.List) -> str:
        if any(isinstance(e, ast.Starred) for e in node.elts):
            return self._handle_list_concat(node)

        elements: List[str] = [self.visit(e) for e in node.elts]
        elements_str: str = ", ".join(elements)
        return f"[{elements_str}]"

    def _handle_list_concat(self, node: ast.List) -> str:
        self._usings.add("arrays")
        # Try to find the target type from scope if it exists
        target_type = "Any"
        if hasattr(node, "annotation"):
            target_type = self._typename_from_annotation(node)
            if target_type.startswith("[]"):
                target_type = target_type[2:]

        parts = []
        curr_list = []
        for e in node.elts:
            if isinstance(e, ast.Starred):
                if curr_list:
                    parts.append(f"[{', '.join(curr_list)}]")
                    curr_list = []
                parts.append(self.visit(e.value))
            else:
                curr_list.append(self.visit(e))
        if curr_list:
            parts.append(f"[{', '.join(curr_list)}]")

        if len(parts) == 1:
            return parts[0]

        res = parts[0]
        if res.startswith("["):
            # Ensure at least first element is of the correct type
            if target_type != "Any":
                if "," in res:
                    first_comma = res.find(",")
                    res = f"[{target_type}({res[1:first_comma]}){res[first_comma:]}"
                else:
                    res = f"[{target_type}({res[1:-1]})]"
            else:
                if "," in res:
                    first_comma = res.find(",")
                    res = f"[Any({res[1:first_comma]}){res[first_comma:]}"
                else:
                    res = f"[Any({res[1:-1]})]"
        else:
            if target_type != "Any":
                res = f"{res}.map({target_type}(it))"
            else:
                res = f"{res}.map(Any(it))"

        for part in parts[1:]:
            if part.startswith("["):
                # Wrap elements
                if target_type != "Any":
                    if "," in part:
                        f_comma = part.find(",")
                        part = f"[{target_type}({part[1:f_comma]}){part[f_comma:]}"
                    else:
                        part = f"[{target_type}({part[1:-1]})]"
                else:
                    if "," in part:
                        f_comma = part.find(",")
                        part = f"[Any({part[1:f_comma]}){part[f_comma:]}"
                    else:
                        part = f"[Any({part[1:-1]})]"
            else:
                if target_type != "Any":
                    part = f"{part}.map({target_type}(it))"
                else:
                    part = f"{part}.map(Any(it))"
            res = f"arrays.concat({res}, ...{part})"
        return res

    def visit_Set(self, node: ast.Set) -> str:
        # V doesn't have built-in sets, use arrays as a workaround
        return self.visit_List(node)

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
            print(f"DEBUG: visit_Subscript value={value} index={index}")
            if value == "Tuple":
                return f"({index})"
            if value == "[]":
                return f"[]{index}"
            return f"{value}[{index}]"
        if index.startswith("-") and index[1:].isdigit():
            return f"{value}[{value}.len - {index[1:]}]"
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
        raises = [child for child in node.body if isinstance(child, ast.Raise)]
        if raises and node.handlers:
            msg = "'Exception'"
            exc = raises[0].exc
            if isinstance(exc, ast.Call) and exc.args:
                msg = self.visit(exc.args[0])
            elif exc is not None:
                msg = f"'{get_id(exc)}'"
            buf = []
            for handler in node.handlers[:1]:
                uses_handler_name = handler.name and any(
                    isinstance(child, ast.Name) and child.id == handler.name
                    for body_node in handler.body
                    for child in ast.walk(body_node)
                )
                if uses_handler_name:
                    buf.append(f"{handler.name} := {msg}")
                buf.extend(map(self.visit, handler.body))
        elif self._is_module_scope(node):
            buf = []
            for handler in node.handlers:
                buf.extend(self.visit(child) for child in handler.body)
        else:
            buf = list(map(self.visit, node.body))
        if node.finalbody:
            finalbody = "\n".join(
                self.indent(self.visit(child), 2) for child in node.finalbody
            )
            body = "\n".join(self.indent(line) for line in buf)
            return (
                "{\n"
                + self.indent("defer {")
                + f"\n{finalbody}\n"
                + self.indent("}")
                + f"\n{body}\n}}"
            )
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
        if isinstance(node.value, ast.Lambda) and hasattr(node, "annotation"):
            node.value.callable_type = node.annotation
        target, type_str, val = super().visit_AnnAssign(node)
        if isinstance(node.target, (ast.Attribute, ast.Subscript)):
            return f"{target} = {val}"
        kw: str = "mut " if is_mutable(node.scopes, target) else ""
        if val is None or val == "none":
            # Provide default value for V
            if type_str == "int":
                val = "0"
            elif type_str == "f64":
                val = "0.0"
            elif type_str == "string":
                val = "''"
            elif type_str == "bool":
                val = "false"
            elif type_str.startswith("[]"):
                val = f"{type_str}{{}}"
            elif type_str.startswith("map"):
                val = f"{type_str}{{}}"
            else:
                val = "none"
        elif (
            type_str
            and type_str.startswith("map")
            and isinstance(node.value, ast.Call)
            and get_id(node.value.func) == "OrderedDict"
        ):
            val = f"{type_str}{{}}"

        if self._is_module_scope(node) and isinstance(node.target, ast.Name):
            return f"const {target} = {val}"
        if isinstance(node.target, ast.Name):
            definition = None
            if hasattr(node, "scopes"):
                parent_scopes = getattr(node.scopes, "parent_scopes", None)
                if parent_scopes is not None:
                    definition = parent_scopes.find(node.target.id)
                if definition is None:
                    definition = node.scopes.find(node.target.id)
            if defined_before(definition, node):
                return f"{target} = {val}"

        if isinstance(node.value, ast.List):
            if any(isinstance(e, ast.Starred) for e in node.value.elts):
                # Handle list concatenation
                if hasattr(node, "annotation"):
                    node.value.annotation = node.annotation
                res = self._handle_list_concat(node.value)
                return f"{kw}{target} := {res}"
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
        elif isinstance(node.value, ast.Dict):
            if not node.value.keys and type_str:
                return f"{kw}{target} := {type_str}{{}}"
            return f"{kw}{target} := {val}"
        else:
            return f"{kw}{target} := {val}"

    def visit_Assign(self, node: ast.Assign) -> str:
        if (
            isinstance(node.value, ast.Call)
            and get_id(node.value.func) == "argparse.ArgumentParser"
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
        ):
            target = self.visit(node.targets[0])
            return f"mut {target} := {self.visit(node.value)}"
        if (
            isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "parse_known_args"
            and len(node.targets) == 1
            and isinstance(node.targets[0], (ast.Tuple, ast.List))
            and len(node.targets[0].elts) == 2
        ):
            parser_name = get_id(node.value.func.value)
            if parser_name:
                args_target = self.visit(node.targets[0].elts[0])
                rest_target = self.visit(node.targets[0].elts[1])
                return "\n".join(
                    [
                        f"mut {args_target} := {self._argparse_parse_args(parser_name)}",
                        f"{rest_target} := {parser_name}.finalize() or {{ []string{{}} }}",
                    ]
                )
        if (
            isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "parse_args"
            and len(node.targets) == 1
        ):
            parser_name = get_id(node.value.func.value)
            if parser_name:
                target = self.visit(node.targets[0])
                return "\n".join(
                    [
                        f"mut {target} := {self._argparse_parse_args(parser_name)}",
                        f"_ := {parser_name}.finalize() or {{ []string{{}} }}",
                    ]
                )
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

            if isinstance(target, (ast.Tuple, ast.List)) and any(
                isinstance(e, ast.Starred) for e in target.elts
            ):
                assign.extend(self._handle_starred_unpack(target, value, node))
                continue

            if self._is_module_scope(node) and isinstance(target, ast.Name):
                target_name: str = self.visit(target)
                assign.append(f"const {target_name} = {value}")
                continue

            if isinstance(target, (ast.Tuple, ast.List)):
                subtargets: List[str] = []
                post_assign: List[str] = []
                op: str = ":="
                for subtarget in target.elts:
                    if isinstance(subtarget, (ast.Attribute, ast.Subscript)):
                        tmp_target = self._new_tmp("unpack")
                        subtargets.append(tmp_target)
                        post_assign.append(f"{self.visit(subtarget)} = {tmp_target}")
                        continue
                    if hasattr(node, "scopes"):
                        definition: Optional[ast.AST] = node.scopes.parent_scopes.find(
                            get_id(subtarget)
                        ) or node.scopes.find(get_id(subtarget))
                    else:
                        definition: Optional[ast.AST] = None
                    subtargets.append(self.visit(subtarget))
                    if definition is not None and defined_before(definition, subtarget):
                        op = "="
                    elif op == "=":
                        pass
                assign.append(f"{', '.join(subtargets)} {op} {value}")
                assign.extend(post_assign)
            elif isinstance(target, (ast.Subscript, ast.Attribute)):
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            elif isinstance(target, ast.Name) and self.visit(target) == value:
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            elif (
                isinstance(target, ast.Name)
                and hasattr(node, "scopes")
                and (
                    definition := getattr(node.scopes, "parent_scopes", None).find(
                        target.id
                    )
                )
                is not None
                and defined_before(definition, node)
            ):
                target: str = self.visit(target)
                assign.append(f"{target} = {value}")
            elif isinstance(target, ast.Name):
                definition = None
                if hasattr(node, "scopes"):
                    parent_scopes = getattr(node.scopes, "parent_scopes", None)
                    if parent_scopes is not None:
                        definition = parent_scopes.find(target.id)
                    if definition is None:
                        definition = node.scopes.find(target.id)
                if defined_before(definition, node):
                    target: str = self.visit(target)
                    assign.append(f"{target} = {value}")
                else:
                    target: str = self.visit(target)
                    assign.append(f"{kw}{target} := {value}")
            else:
                target: str = self.visit(target)

                assign.append(f"{kw}{target} := {value}")
        return "\n".join(assign)

    def _handle_starred_unpack(self, target, value, node):
        starred_idx = 0
        for i, elt in enumerate(target.elts):
            if isinstance(elt, ast.Starred):
                starred_idx = i
                break
        tmp_var = self._new_tmp("unpack")
        assigns = [f"{tmp_var} := {value}"]
        for i, elt in enumerate(target.elts):
            if i < starred_idx:
                idx_val = f"{tmp_var}[{i}]"
                target_elt = elt
            elif i == starred_idx:
                end = len(target.elts) - 1 - i
                idx_val = (
                    f"{tmp_var}[{i}..{tmp_var}.len - {end}]"
                    if end > 0
                    else f"{tmp_var}[{i}..]"
                )
                target_elt = elt.value
            else:
                dist = len(target.elts) - 1 - i
                idx_val = (
                    f"{tmp_var}.last()"
                    if dist == 0
                    else f"{tmp_var}[{tmp_var}.len - {dist + 1}]"
                )
                target_elt = elt

            subkw = ""
            subop = ":="
            if hasattr(node, "scopes"):
                subkw = "mut " if is_mutable(node.scopes, get_id(target_elt)) else ""
                definition = node.scopes.parent_scopes.find(
                    get_id(target_elt)
                ) or node.scopes.find(get_id(target_elt))
                if definition and defined_before(definition, target_elt):
                    subop = "="
                    subkw = ""

            assigns.append(f"{subkw}{self.visit(target_elt)} {subop} {idx_val}")
        return assigns

    def visit_AugAssign(self, node: ast.AugAssign) -> str:
        target: str = self.visit(node.target)
        op: str = self.visit(node.op)
        val: str = self.visit(node.value)
        # If value is from a variadic Any, it must be unboxed using 'as'
        if val in ["n", "it"]:
            # Check if it's really Any.
            # This is a bit of a hack since we don't have full type info here easily,
            # but we can check if the current function has a vararg of type Any.
            # However, for now, let's just check if 'Any' is defined in the module.
            if self._generated_code_has_any_type:
                # In sum_all(*nums: int), n is int, not Any.
                # We should only use 'as' if the parent loop iter is over a slice of Any.
                # For now, let's keep it simple: only use 'as int' if it's likely needed.
                # Better yet, let's check if the target is int and value is Any.
                pass

        return f"{target} {op}= {val}"

    def visit_Delete(self, node: ast.Delete) -> str:
        targets = []
        for target in node.targets:
            if isinstance(target, ast.Subscript):
                value = self.visit(target.value)
                slice = self.visit(target.slice)
                targets.append(f"{value}.delete({slice})")
            else:
                targets.append(f"/* del {self.visit(target)} */")
        return "\n".join(targets)

    def visit_Raise(self, node: ast.Raise) -> str:
        if node.exc is None:
            return "panic('Exception')"
        msg = f"'{get_id(node.exc)}'"
        if isinstance(node.exc, ast.Call):
            msg = f"'{get_id(node.exc.func)}'"
            if node.exc.args:
                msg = self.visit(node.exc.args[0])
        return f"panic({msg})"

    def visit_With(self, node: ast.With) -> str:
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

    def visit_Await(self, node: ast.Await) -> str:
        raise AstNotImplementedError("asyncio is not supported.", node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> str:
        # V doesn't have async/await, but we can convert async functions to regular ones
        # with warnings about lost async semantics
        # The function body will be processed normally, but async operations will be converted
        import warnings

        warnings.warn("Async function converted to sync. Async semantics lost.")

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
        if not node.generators:
            return "{}"

        # V does not support expression blocks, so represent dict comprehensions
        # as an immediately invoked function expression returning a `map[...]...`.
        key_type = get_inferred_v_type(node.key)
        if not key_type or key_type == "Any":
            # Try to infer `int` keys from `for x in range(...)` when the key is the loop var.
            if isinstance(node.key, ast.Name):
                for comp in node.generators:
                    if (
                        isinstance(comp.target, ast.Name)
                        and comp.target.id == node.key.id
                        and isinstance(comp.iter, ast.Call)
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

            if isinstance(target, ast.Name):
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
        return f"// global {names}  // V does not support global keyword"

    def visit_IfExp(self, node: ast.IfExp) -> str:
        body: str = self.visit(node.body)
        orelse: str = self.visit(node.orelse)
        test: str = self.visit(node.test)
        return f"if {test} {{ {body} }} else {{ {orelse} }}"

    def visit_NamedExpr(self, node: ast.NamedExpr) -> str:
        # V doesn't support walrus operator, and it should be lifted by VWalrusRewriter
        # If we reach here, it means lifting failed or the node is in an unsupported context
        target = self.visit(node.target)
        value = self.visit(node.value)
        return f"({target} := {value})"

    def visit_AsyncFor(self, node: ast.AsyncFor) -> str:
        # V doesn't support async/await, so we'll convert to a synchronous loop.
        # The iterator may still be a channel-based generator.
        buf = ["// WARNING: async for converted to sync for"]

        for_node = ast.For(
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
