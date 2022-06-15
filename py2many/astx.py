import ast

from dataclasses import dataclass, field
from enum import IntEnum
from typing import List, Optional, Tuple


class LifeTime(IntEnum):
    UNKNOWN = 0
    STATIC = 1


@dataclass
class ASTxName(ast.Name):
    lifetime: LifeTime = LifeTime.UNKNOWN
    assigned_from: Optional["ASTx"] = None


@dataclass
class ASTxClassDef(ast.ClassDef):
    is_dataclass: bool = False


@dataclass
class ASTxFunctionDef(ast.FunctionDef):
    mutable_vars: List[str] = field(default_factory=list)
    python_main: bool = False


@dataclass
class ASTxModule(ast.Module):
    __file__: Optional[str] = None


@dataclass
class ASTxSubscript(ast.Subscript):
    container_type: Optional[Tuple[str, str]] = None
    generic_container_type: Optional[Tuple[str, str]] = None


@dataclass
class ASTxIf(ast.If):
    unpack: bool = False


@dataclass
class ASTx(ast.AST):
    annotation: ASTxName
    rewritten: bool = False
    lhs: bool = False
    scopes: List["ASTx"] = field(default_factory=list)
    id: Optional[str] = None
