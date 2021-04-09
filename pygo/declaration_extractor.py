from py2many.declaration_extractor import (
    DeclarationExtractor as CommonDeclarationExtractor,
)
from .clike import go_type_map


class DeclarationExtractor(CommonDeclarationExtractor):
    def __init__(self, transpiler):
        super().__init__(transpiler)
        self._type_map = go_type_map
