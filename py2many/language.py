import ast
from dataclasses import dataclass, field
from typing import Callable, List, Optional

from .clike import CLikeTranspiler


@dataclass
class LanguageSettings:
    transpiler: CLikeTranspiler
    ext: str
    display_name: str
    formatter: Optional[List[str]] = None
    indent: Optional[int] = None
    rewriters: List[ast.NodeVisitor] = field(default_factory=list)
    transformers: List[Callable] = field(default_factory=list)
    post_rewriters: List[ast.NodeVisitor] = field(default_factory=list)
    linter: Optional[List[str]] = None
    # Create a language specific project structure
    create_project: Optional[List[str]] = None
    # Rust likes source files to live in {project}/src for example
    project_subdir: Optional[str] = None
    ignore_formatter_errors: bool = False

    def __hash__(self):
        f = tuple(self.formatter) if self.formatter is not None else ()
        l = tuple(self.linter) if self.linter is not None else ()
        return hash((self.transpiler, f, l))
