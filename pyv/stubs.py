import ast
from typing import Callable, Dict, List


def visit_str_join(self, node: ast.Call, vargs: List[str]) -> str:
    if len(vargs) == 1:
        # Python: sep.join(iterable) -> V: iterable.join(sep)
        sep = self.visit(node.func.value)
        return f"{vargs[0]}.join({sep})"
    return "/* join requires 1 argument */"


def _use_regex(self) -> bool:
    self._usings.add("regex")
    return True


def _re_expr(self, vargs: List[str], args: str, ret_type: str, body: str) -> str:
    _use_regex(self)
    return (
        f"(fn({args}) {ret_type} {{ mut re := regex.regex_opt(p) "
        f"or {{ panic(err) }}; {body} }}({', '.join(vargs)}))"
    )


STDLIB_DISPATCH_TABLE: Dict[str, Callable] = {
    "str.lower": lambda self, node, vargs: f"{self.visit(node.func.value)}.to_lower()",
    "str.upper": lambda self, node, vargs: f"{self.visit(node.func.value)}.to_upper()",
    "str.capitalize": lambda self, node, vargs: f"{self.visit(node.func.value)}.capitalize()",
    "str.title": lambda self, node, vargs: f"{self.visit(node.func.value)}.title()",
    "str.strip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_space()",
    "str.lstrip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_left(' ')",
    "str.rstrip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_right(' ')",
    "str.find": lambda self, node, vargs: f"({self.visit(node.func.value)}.index({vargs[0]}) or {{ -1 }})",
    "str.replace": lambda self, node, vargs: f"{self.visit(node.func.value)}.replace({', '.join(vargs)})",
    "str.split": lambda self, node, vargs: (
        f"{self.visit(node.func.value)}.split({vargs[0]})"
        if vargs
        else f"{self.visit(node.func.value)}.fields()"
    ),
    "str.join": visit_str_join,
    "str.isalpha": lambda self, node, vargs: f"{self.visit(node.func.value)}.bytes().all(it.is_letter())",
    "str.isdigit": lambda self, node, vargs: f"{self.visit(node.func.value)}.bytes().all(it.is_digit())",
    "str.isspace": lambda self, node, vargs: f"({self.visit(node.func.value)}.trim_space() == '')",
    # re module
    "re.search": lambda self, node, vargs: _re_expr(
        self, vargs, "p string, s string", "bool", "return re.find_all_str(s).len > 0"
    ),
    "re.match": lambda self, node, vargs: _re_expr(
        self,
        [f"'^' + {vargs[0]}", vargs[1]],
        "p string, s string",
        "bool",
        "return re.find_all_str(s).len > 0",
    ),
    "re.findall": lambda self, node, vargs: _re_expr(
        self, vargs, "p string, s string", "[]string", "return re.find_all_str(s)"
    ),
    "re.sub": lambda self, node, vargs: _re_expr(
        self, vargs, "p string, r string, s string", "string", "return re.replace(s, r)"
    ),
    "re.split": lambda self, node, vargs: _re_expr(
        self, vargs, "p string, s string", "[]string", "return re.split(s)"
    ),
    "re.compile": lambda self, node, vargs: _use_regex(self)
    and f"regex.regex_opt({vargs[0]}) or {{ panic(err) }}",
}
