from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Protocol


class CppRenderable(Protocol):
    def render(self) -> str: ...


def _load_tree_sitter_cpp():
    try:
        import tree_sitter_cpp
        from tree_sitter import Language, Parser
    except ImportError:
        return None

    parser = Parser()
    cpp_language = tree_sitter_cpp.language()
    try:
        language = Language(cpp_language)
    except TypeError:
        language = cpp_language

    if hasattr(parser, "set_language"):
        parser.set_language(language)
    else:
        parser.language = language
    return parser


def _node_has_error(node) -> bool:
    if getattr(node, "has_error", False):
        return True
    return any(_node_has_error(child) for child in node.children)


@dataclass(frozen=True)
class CppTreeSitterNode:
    """A C++ syntax subtree parsed by tree-sitter."""

    source: str
    kind: str = "translation_unit"
    has_error: bool = False
    _tree: object | None = field(default=None, repr=False, compare=False)

    @classmethod
    def parse(cls, source: str) -> "CppTreeSitterNode":
        parser = _load_tree_sitter_cpp()
        if parser is None:
            return cls(source=source)

        tree = parser.parse(source.encode("utf-8"))
        root = tree.root_node
        return cls(
            source=source,
            kind=root.type,
            has_error=_node_has_error(root),
            _tree=tree,
        )

    @property
    def tree(self):
        return self._tree

    def render(self) -> str:
        return self.source


class CppNode(str):
    """A C++ syntax fragment backed by a tree-sitter parse.

    The C++ transpiler still has expression-level composition logic that expects
    string operations. Subclassing str lets that logic keep working while
    visitors move toward returning renderable C++ nodes.
    """

    node: CppTreeSitterNode

    def __new__(cls, source: str | CppRenderable) -> "CppNode":
        if isinstance(source, CppNode):
            return source
        source_str = source.render() if hasattr(source, "render") else str(source)
        obj = str.__new__(cls, source_str)
        obj.node = CppTreeSitterNode.parse(source_str)
        return obj

    @property
    def tree(self):
        return self.node.tree

    @property
    def kind(self) -> str:
        return self.node.kind

    @property
    def has_error(self) -> bool:
        return self.node.has_error

    def render(self) -> str:
        return str(self)


class CppCall(CppNode):
    def __new__(
        cls,
        function: str | CppRenderable,
        args: Iterable[str | CppRenderable],
    ) -> "CppCall":
        rendered_args = ", ".join(str(arg) for arg in args)
        return super().__new__(cls, f"{function}({rendered_args})")


class CppReturn(CppNode):
    def __new__(cls, value: str | CppRenderable | None = None) -> "CppReturn":
        if value is None:
            return super().__new__(cls, "return;")
        return super().__new__(cls, f"return {value};")


class CppAssignment(CppNode):
    def __new__(
        cls, target: str | CppRenderable, value: str | CppRenderable
    ) -> "CppAssignment":
        return super().__new__(cls, f"{target} = {value};")


class CppAugAssignment(CppNode):
    def __new__(
        cls,
        target: str | CppRenderable,
        op: str | CppRenderable,
        value: str | CppRenderable,
    ) -> "CppAugAssignment":
        return super().__new__(cls, f"{target} {op}= {value};")


class CppDeclaration(CppNode):
    def __new__(
        cls,
        typename: str | CppRenderable,
        target: str | CppRenderable,
        value: str | CppRenderable,
        suffix: str = "",
    ) -> "CppDeclaration":
        return super().__new__(cls, f"{typename} {target} = {value};{suffix}")


class CppExprStatement(CppNode):
    def __new__(cls, expression: str | CppRenderable) -> "CppExprStatement":
        rendered = str(expression).strip()
        if not rendered.endswith(";"):
            rendered += ";"
        return super().__new__(cls, rendered)


class CppFunction(CppNode):
    def __new__(
        cls,
        signature: str | CppRenderable,
        body: Iterable[str | CppRenderable],
    ) -> "CppFunction":
        rendered_body = "\n".join(str(item) for item in body)
        return super().__new__(cls, f"{signature} {{\n{rendered_body}\n}}\n")


@dataclass(frozen=True)
class CppRawItem:
    """A C++ item or statement subtree kept as source until visitors are typed."""

    node: CppTreeSitterNode

    @classmethod
    def from_source(cls, source: str) -> "CppRawItem":
        if isinstance(source, CppNode):
            return cls(source.node)
        return cls(CppTreeSitterNode.parse(source))

    def render(self) -> str:
        return self.node.render()


@dataclass(frozen=True)
class CppSourceFile:
    items: tuple

    @classmethod
    def from_items(cls, items: Iterable[str | CppRenderable]) -> "CppSourceFile":
        renderable_items: list[CppRenderable] = []
        for item in items:
            if hasattr(item, "render"):
                renderable_items.append(item)
            elif isinstance(item, str):
                if item:
                    renderable_items.append(CppRawItem.from_source(item))
            else:
                renderable_items.append(CppNode(str(item)))
        return cls(tuple(renderable_items))

    def render(self) -> str:
        rendered_items = []
        for item in self.items:
            rendered = item.render()
            rendered = rendered.rstrip("\n") + ("\n" if rendered.endswith("\n") else "")
            rendered_items.append(rendered)
        return "\n".join(rendered_items)


class CppRenderer:
    def render(self, node: CppRenderable) -> str:
        return node.render()
