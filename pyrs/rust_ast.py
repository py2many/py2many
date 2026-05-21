from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Protocol


class RustRenderable(Protocol):
    def render(self) -> str: ...


def _load_tree_sitter_rust():
    try:
        import tree_sitter_rust
        from tree_sitter import Language, Parser
    except ImportError:
        return None

    parser = Parser()
    rust_language = tree_sitter_rust.language()
    try:
        language = Language(rust_language)
    except TypeError:
        language = rust_language

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
class RustTreeSitterNode:
    """A Rust syntax subtree parsed by tree-sitter."""

    source: str
    kind: str = "source_file"
    has_error: bool = False
    _tree: object | None = field(default=None, repr=False, compare=False)

    @classmethod
    def parse(cls, source: str) -> "RustTreeSitterNode":
        parser = _load_tree_sitter_rust()
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


class RustNode(str):
    """A Rust syntax fragment backed by a tree-sitter parse.

    The Rust transpiler still has a lot of expression-level composition logic
    that expects string operations. Subclassing str lets that logic keep working
    while making the visitor return value a renderable Rust node.
    """

    node: RustTreeSitterNode

    def __new__(cls, source: str | RustRenderable) -> "RustNode":
        if isinstance(source, RustNode):
            return source
        source_str = source.render() if hasattr(source, "render") else str(source)
        obj = str.__new__(cls, source_str)
        obj.node = RustTreeSitterNode.parse(source_str)
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


class RustCall(RustNode):
    def __new__(
        cls,
        function: str | RustRenderable,
        args: Iterable[str | RustRenderable],
        suffix: str = "",
    ) -> "RustCall":
        rendered_args = ", ".join(str(arg) for arg in args)
        return super().__new__(cls, f"{function}({rendered_args}){suffix}")


class RustReturn(RustNode):
    def __new__(cls, value: str | RustRenderable | None = None) -> "RustReturn":
        if value is None:
            return super().__new__(cls, "return;")
        return super().__new__(cls, f"return {value};")


class RustAssignment(RustNode):
    def __new__(
        cls, target: str | RustRenderable, value: str | RustRenderable
    ) -> "RustAssignment":
        return super().__new__(cls, f"{target} = {value};")


class RustAugAssignment(RustNode):
    def __new__(
        cls,
        target: str | RustRenderable,
        op: str | RustRenderable,
        value: str | RustRenderable,
    ) -> "RustAugAssignment":
        return super().__new__(cls, f"{target} {op}= {value};")


class RustLet(RustNode):
    def __new__(
        cls,
        target: str | RustRenderable,
        value: str | RustRenderable,
        keyword: str = "let",
        typename: str | None = None,
    ) -> "RustLet":
        type_annotation = f": {typename}" if typename else ""
        return super().__new__(cls, f"{keyword} {target}{type_annotation} = {value};")


class RustExprStatement(RustNode):
    def __new__(cls, expression: str | RustRenderable) -> "RustExprStatement":
        rendered = str(expression).strip()
        if not rendered.endswith(";"):
            rendered += ";"
        return super().__new__(cls, rendered)


class RustFunction(RustNode):
    def __new__(
        cls,
        signature: str | RustRenderable,
        body: Iterable[str | RustRenderable],
        return_success: str = "",
        prefix: str = "",
    ) -> "RustFunction":
        rendered_body = "\n".join(str(item) for item in body)
        return super().__new__(
            cls, f"{prefix}{signature} {{\n{rendered_body}\n {return_success}}}\n"
        )


class RustForLoop(RustNode):
    def __new__(
        cls,
        target: str | RustRenderable,
        iterable: str | RustRenderable,
        body: Iterable[str | RustRenderable],
    ) -> "RustForLoop":
        rendered_body = "\n".join(str(item) for item in body)
        return super().__new__(
            cls, f"for {target} in {iterable} {{\n{rendered_body}\n}}"
        )


class RustWhileLoop(RustNode):
    def __new__(
        cls, test: str | RustRenderable, body: Iterable[str | RustRenderable]
    ) -> "RustWhileLoop":
        rendered_body = "\n".join(str(item) for item in body)
        return super().__new__(cls, f"while {test} {{\n{rendered_body}\n}}")


class RustLoop(RustNode):
    def __new__(cls, body: Iterable[str | RustRenderable]) -> "RustLoop":
        rendered_body = "\n".join(str(item) for item in body)
        return super().__new__(cls, "loop {{\n{}\n}}\n".format(rendered_body))


class RustIf(RustNode):
    def __new__(
        cls,
        test: str | RustRenderable,
        body: Iterable[str | RustRenderable],
        orelse: Iterable[str | RustRenderable] | None = None,
    ) -> "RustIf":
        rendered_body = "\n".join(str(item) for item in body)
        rendered = f"if {test} {{\n{rendered_body}\n}}"
        if orelse:
            rendered_orelse = "\n".join(str(item) for item in orelse)
            rendered += f" else {{\n{rendered_orelse}\n}}"
        return super().__new__(cls, rendered)


class RustMacroCall(RustNode):
    def __new__(
        cls,
        macro: str,
        args: Iterable[str | RustRenderable],
        suffix: str = ";",
        separator: str = ", ",
    ) -> "RustMacroCall":
        rendered_args = separator.join(str(arg) for arg in args)
        return super().__new__(cls, f"{macro}!({rendered_args}){suffix}")


class RustAwait(RustNode):
    def __new__(cls, value: str | RustRenderable) -> "RustAwait":
        return super().__new__(cls, f"{value}.await")


class RustYield(RustNode):
    def __new__(cls, value: str | RustRenderable) -> "RustYield":
        return super().__new__(cls, f"yield {value};")


@dataclass(frozen=True)
class RustRawItem:
    """A Rust item or statement subtree kept as source until visitors are typed."""

    node: RustTreeSitterNode

    @classmethod
    def from_source(cls, source: str) -> "RustRawItem":
        if isinstance(source, RustNode):
            return cls(source.node)
        return cls(RustTreeSitterNode.parse(source))

    def render(self) -> str:
        return self.node.render()


@dataclass(frozen=True)
class RustSourceFile:
    items: tuple

    @classmethod
    def from_items(cls, items: Iterable[str | RustRenderable]) -> "RustSourceFile":
        renderable_items: list[RustRenderable] = []
        for item in items:
            if hasattr(item, "render"):
                renderable_items.append(item)
            elif isinstance(item, str):
                if item:
                    renderable_items.append(RustRawItem.from_source(item))
            else:
                renderable_items.append(RustNode(str(item)))
        return cls(tuple(renderable_items))

    def render(self) -> str:
        rendered_items = []
        for item in self.items:
            rendered = item.render()
            rendered = rendered.rstrip("\n") + ("\n" if rendered.endswith("\n") else "")
            rendered_items.append(rendered)
        return "\n".join(rendered_items).replace("*/\npub ", "*/\n\npub ")


class RustRenderer:
    def render(self, node: RustRenderable) -> str:
        return node.render()
