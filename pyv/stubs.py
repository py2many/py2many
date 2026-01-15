import ast
from typing import Callable, Dict, List, Optional, Union

def visit_str_join(self, node: ast.Call, vargs: List[str]) -> str:
    if len(vargs) == 1:
        # Python: sep.join(iterable) -> V: iterable.join(sep)
        sep = self.visit(node.func.value)
        return f"{vargs[0]}.join({sep})"
    return f"/* join requires 1 argument */"

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
    "str.split": lambda self, node, vargs: f"{self.visit(node.func.value)}.split({vargs[0]})" if vargs else f"{self.visit(node.func.value)}.fields()",
    "str.join": visit_str_join,
    "str.isalpha": lambda self, node, vargs: f"{self.visit(node.func.value)}.bytes().all(it.is_letter())",
    "str.isdigit": lambda self, node, vargs: f"{self.visit(node.func.value)}.bytes().all(it.is_digit())",
    "str.isspace": lambda self, node, vargs: f"({self.visit(node.func.value)}.trim_space() == '')",
}
