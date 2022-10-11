import ast
from typing import Optional

from py2many.ast_helpers import get_id


def pycall_import(self, node: ast.Call, mod_name: str, opt_name: Optional[str] = None):
    self._usings.add("PyCall")
    if opt_name:
        self._pycall_imports.add(opt_name)
        import_stmt = f'{opt_name} = pyimport("{mod_name}")'
    else:
        self._pycall_imports.add(mod_name)
        import_stmt = f'{mod_name} = pyimport("{mod_name}")'
    self._globals.add(import_stmt)


def verify_types(annotation: ast.AST, t: str):
    """Verifies if the provided type is in the annotation"""
    if isinstance(annotation, ast.Name):
        return get_id(annotation) == t
    elif isinstance(annotation, ast.Subscript):
        return verify_types(annotation.slice, t)
    elif isinstance(annotation, (ast.Tuple, ast.List)):
        type_checks = []
        for elt in annotation.elts:
            type_checks.append(verify_types(elt, t))
        return any(type_checks)
    return False
