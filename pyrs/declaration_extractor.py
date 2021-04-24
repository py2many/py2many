from py2many.declaration_extractor import (
    DeclarationExtractor as CommonDeclarationExtractor,
)
from .inference import RUST_TYPE_MAP


class DeclarationExtractor(CommonDeclarationExtractor):
    def __init__(self, transpiler):
        super().__init__(transpiler)
        self._type_map = RUST_TYPE_MAP

    # TODO better type infering based on variable init
    def type_by_initialization(self, init_str):
        if init_str == "vec![]":
            return "Vec<_>"
        elif init_str == "HashMap::new()":
            return "HashMap<_,_>"
        elif init_str == "None":
            return "Option<_>"
        elif init_str == "true" or init_str == "false":
            return "bool"
        else:
            return None
