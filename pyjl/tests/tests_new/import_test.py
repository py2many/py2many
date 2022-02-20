# Testing imports
import datetime as dt
import json as js

# Testing import with local module
from class_scopes import ScopeTest

class ScopeExtension(ScopeTest):
    def __init__(self, id: str) -> None:
        self.id: str = id

    def test2(self):
        return "test2"

if __name__ == "__main__":
    sc_ext = ScopeExtension("1")
    assert sc_ext.test() == "test"
    assert sc_ext.test2() == "test2"


