from py2many.declaration_extractor import (
    DeclarationExtractor as CommonDeclarationExtractor,
)
from .clike import julia_type_map


class DeclarationExtractor(CommonDeclarationExtractor):
    def __init__(self, transpiler):
        super().__init__(transpiler)
        self._type_map = julia_type_map
