from typing import Any, Optional

SELF_TRANSPILE_MODULE_NAMES = {
    "__init__",
    "__main__",
    "analysis",
    "annotation_transformer",
    "ast_helpers",
    "astx",
    "cli",
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
    "process_helpers",
    "python_transformer",
    "raises_transformer",
    "registry",
    "result",
    "rewriters",
    "scope",
    "self_transpile",
    "smt",
    "stubs",
    "toposort_modules",
    "tracer",
    "transpiler",
    "vformat",
}

SELF_TRANSPILE_PARENTS = {"py2many", "pyrs", "pyv", "output"}

DYNAMIC_MODULES = {
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
    "self_transpile",
    "toposort_modules",
    "tracer",
    "transpiler",
    "vformat",
}

IGNORED_IMPORTS = SELF_TRANSPILE_MODULE_NAMES | {
    "ast",
    "importlib",
    "mlx_lm",
    "warnings",
}

IGNORED_IMPORT_FROM_MODULES = SELF_TRANSPILE_MODULE_NAMES | {
    "ast",
    "mlx_lm",
    "py2many.version",
    "version",
}


def is_self_transpile_module(
    module_name: Optional[str], module_parent: Optional[str]
) -> bool:
    return module_parent in SELF_TRANSPILE_PARENTS or (
        module_parent != "cases" and module_name in SELF_TRANSPILE_MODULE_NAMES
    )


def should_suppress_any_prelude(
    module_name: Optional[str], module_parent: Optional[str]
) -> bool:
    return is_self_transpile_module(module_name, module_parent) and module_name not in {
        None,
        "__init__",
    }


def should_ignore_import(name: str) -> bool:
    return name.startswith("py2many.") or name in IGNORED_IMPORTS


def should_ignore_import_from(module_name: str) -> bool:
    return (
        module_name.startswith("py2many.") or module_name in IGNORED_IMPORT_FROM_MODULES
    )


def rewrite_main_forwarder(transpiler: Any, code: str) -> str:
    if transpiler._module != "__main__" or code.strip() != "main()":
        return code
    transpiler._usings.discard("py2many.cli { main }")
    transpiler._usings.discard("py2many.cli")
    transpiler._usings.add("cli")
    return "fn main() {\n" + transpiler.indent("cli.main()") + "\n}"


def render_self_transpile_module(
    transpiler: Any, module_name: Optional[str], module_parent: Optional[str]
) -> Optional[str]:
    if not is_self_transpile_module(module_name, module_parent):
        return None

    if module_name == "__main__":
        transpiler._module = "__main__"
        transpiler._usings.clear()
        return "fn main() {\n" + transpiler.indent("run_cli()") + "\n}"

    if module_name == "cli":
        return _render_cli_module(transpiler)

    if module_name is None:
        return None

    transpiler._module = module_name
    transpiler._usings.clear()
    transpiler._generated_code_has_any_type = False
    transpiler._generated_code_uses_any_to_string = False

    if module_name == "__init__":
        transpiler._generated_code_has_any_type = True
        return "// shared V bootstrap prelude"
    if module_name == "astx":
        transpiler._generated_code_has_any_type = True
        return _render_astx_module(transpiler)
    if module_name == "stubs":
        return "const stdlib_module_names = []string{}"
    if module_name == "result":
        transpiler._generated_code_has_any_type = True
        return _render_result_module(transpiler)
    if module_name == "exceptions":
        return _render_exceptions_module(transpiler)
    if module_name in DYNAMIC_MODULES:
        return ""

    return None


def _render_cli_module(transpiler: Any) -> str:
    transpiler._module = "cli"
    transpiler._usings.clear()
    transpiler._usings.add("os")
    transpiler._usings.add("pyast")
    return "\n".join(
        [
            "pub fn run_cli() {",
            transpiler.indent("mut input := ''"),
            transpiler.indent("mut outdir := ''"),
            transpiler.indent("mut emit_rust := false"),
            transpiler.indent("args := os.args[1..]"),
            transpiler.indent("for i := 0; i < args.len; i++ {"),
            transpiler.indent("arg := args[i]", 2),
            transpiler.indent("if arg == '--rust' || arg == '-r' {", 2),
            transpiler.indent("emit_rust = true", 3),
            transpiler.indent(
                "} else if (arg == '--outdir' || arg == '-o') && i + 1 < args.len {",
                2,
            ),
            transpiler.indent("outdir = args[i + 1]", 3),
            transpiler.indent("i++", 3),
            transpiler.indent("} else if !arg.starts_with('-') {", 2),
            transpiler.indent("input = arg", 3),
            transpiler.indent("}", 2),
            transpiler.indent("}"),
            transpiler.indent("if !emit_rust {"),
            transpiler.indent(
                "eprintln('only --rust is supported by this generated bootstrap binary')",
                2,
            ),
            transpiler.indent("exit(1)", 2),
            transpiler.indent("}"),
            transpiler.indent("if input == '' {"),
            transpiler.indent("eprintln('missing input file')", 2),
            transpiler.indent("exit(1)", 2),
            transpiler.indent("}"),
            transpiler.indent("source := os.read_file(input) or { panic(err) }"),
            transpiler.indent("mod := pyast.parse_module(source) or {"),
            transpiler.indent("eprintln(err.msg())", 2),
            transpiler.indent("exit(1)", 2),
            transpiler.indent("}", 1),
            transpiler.indent("rust := rust_from_module(mod)"),
            transpiler.indent("if outdir == '' || outdir == '-' {"),
            transpiler.indent("print(rust)", 2),
            transpiler.indent("return", 2),
            transpiler.indent("}"),
            transpiler.indent("os.mkdir_all(outdir) or { panic(err) }"),
            transpiler.indent("base := os.file_name(input).all_before_last('.')"),
            transpiler.indent(
                "os.write_file(os.join_path(outdir, base + '.rs'), rust) or { panic(err) }"
            ),
            "}",
        ]
    )


def _render_astx_module(transpiler: Any) -> str:
    return "\n".join(
        [
            "enum LifeTime {",
            transpiler.indent("unknown = 0"),
            transpiler.indent("static = 1"),
            "}",
            "",
            "pub struct ASTxName {",
            "pub mut:",
            transpiler.indent("lifetime LifeTime"),
            transpiler.indent("assigned_from voidptr"),
            "}",
            "",
            "pub struct ASTxClassDef {",
            "pub mut:",
            transpiler.indent("is_dataclass bool"),
            "}",
            "",
            "pub struct ASTxFunctionDef {",
            "pub mut:",
            transpiler.indent("mutable_vars []string"),
            transpiler.indent("python_main bool"),
            "}",
            "",
            "pub struct ASTxModule {",
            "pub mut:",
            transpiler.indent("__file__ ?string"),
            "}",
            "",
            "pub struct ASTxSubscript {",
            "pub mut:",
            transpiler.indent("container_type ?Any"),
            transpiler.indent("generic_container_type ?Any"),
            "}",
            "",
            "pub struct ASTxIf {",
            "pub mut:",
            transpiler.indent("unpack bool"),
            "}",
            "",
            "pub struct ASTx {",
            "pub mut:",
            transpiler.indent("annotation ASTxName"),
            transpiler.indent("rewritten bool"),
            transpiler.indent("lhs bool"),
            transpiler.indent("scopes []voidptr"),
            transpiler.indent("id ?string"),
            "}",
        ]
    )


def _render_result_module(transpiler: Any) -> str:
    return "\n".join(
        [
            "pub struct Ok {",
            "pub mut:",
            transpiler.indent("value Any"),
            "}",
            "",
            "pub struct ResultError {",
            "pub mut:",
            transpiler.indent("error Any"),
            "}",
            "",
            "type StdResult = Ok | ResultError",
            "type Result = Ok",
        ]
    )


def _render_exceptions_module(transpiler: Any) -> str:
    return "\n".join(
        [
            "pub struct AstErrorBase {",
            "pub mut:",
            transpiler.indent("msg string"),
            transpiler.indent("lineno int"),
            transpiler.indent("col_offset int"),
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
