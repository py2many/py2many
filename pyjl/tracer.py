from typing import Optional
import ast

def _lookup_class(name, scopes) -> Optional[ast.ClassDef]:
    for scope in scopes:
        for entry in scope.body:
            if isinstance(entry, ast.ClassDef):
                if entry.name == name:
                    return entry
    return None


def is_class(name, scopes):
    entry = _lookup_class(name, scopes)
    return entry is not None