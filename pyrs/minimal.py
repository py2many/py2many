from typing import List

from pyast import (
    AttributeExpr,
    CallExpr,
    CompareExpr,
    Expr,
    ExprStmt,
    IfStmt,
    ImportStmt,
    IntExpr,
    Module,
    NameExpr,
    PassStmt,
    Stmt,
    StringExpr,
)


def rust_string_literal(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def rust_expr(expr: Expr) -> str:
    if isinstance(expr, IntExpr):
        return str(expr.value)
    if isinstance(expr, StringExpr):
        return '"' + rust_string_literal(expr.value) + '"'
    if isinstance(expr, NameExpr):
        if expr.name == "True":
            return "true"
        if expr.name == "False":
            return "false"
        return expr.name
    if isinstance(expr, CallExpr):
        args: List[str] = []
        for arg in expr.args:
            args.append(rust_expr(arg))
        return rust_expr(expr.func) + "(" + ", ".join(args) + ")"
    if isinstance(expr, AttributeExpr):
        return rust_expr(expr.value) + "." + expr.attr
    return ""


def rust_print(args: List[Expr], level: int) -> str:
    indent = "\t" * level
    if len(args) == 0:
        return indent + "println!();"
    rendered: List[str] = []
    for arg in args:
        rendered.append(rust_expr(arg))
    fmt: List[str] = []
    for _ in rendered:
        fmt.append("{}")
    return indent + 'println!("' + " ".join(fmt) + '", ' + ", ".join(rendered) + ");"


def is_main_guard(stmt: IfStmt) -> bool:
    if isinstance(stmt.test, CompareExpr):
        test = stmt.test
        if len(test.ops) != 1 or test.ops[0] != "Eq" or len(test.comparators) != 1:
            return False
        comparator = test.comparators[0]
        if isinstance(test.left, NameExpr) and isinstance(comparator, StringExpr):
            left = test.left
            right = comparator
            return left.name == "__name__" and right.value == "__main__"
    return False


def rust_stmt(stmt: Stmt, level: int) -> List[str]:
    indent = "\t" * level
    if isinstance(stmt, PassStmt):
        return []
    if isinstance(stmt, ImportStmt):
        return []
    if isinstance(stmt, ExprStmt):
        if isinstance(stmt.value, CallExpr):
            call = stmt.value
            if isinstance(call.func, NameExpr):
                name = call.func
                if name.name == "print":
                    return [rust_print(call.args, level)]
                return [indent + name.name + "();"]
            if isinstance(call.func, AttributeExpr):
                attr = call.func
                if isinstance(attr.value, NameExpr):
                    base = attr.value
                    if (
                        base.name == "sys"
                        and attr.attr == "exit"
                        and len(call.args) == 1
                    ):
                        return [
                            indent
                            + "std::process::exit("
                            + rust_expr(call.args[0])
                            + ");"
                        ]
        return []
    if isinstance(stmt, IfStmt):
        if is_main_guard(stmt):
            lines: List[str] = []
            for child in stmt.body:
                child_lines = rust_stmt(child, level)
                for line in child_lines:
                    lines.append(line)
            return lines
    return []


def rust_from_module(mod: Module) -> str:
    body: List[str] = []
    for stmt in mod.body:
        lines = rust_stmt(stmt, 1)
        for line in lines:
            body.append(line)
    return "fn main() {\n" + "\n".join(body) + "\n}\n"
