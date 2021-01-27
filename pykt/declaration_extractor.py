from common.declaration_extractor import (
    DeclarationExtractor as CommonDeclarationExtractor,
)
from .clike import kotlin_type_map


class DeclarationExtractor(CommonDeclarationExtractor):
    def __init__(self, transpiler):
        super().__init__(transpiler)
        self._type_map = kotlin_type_map
