import datetime as dt
import json as js

# Testing import with local module
from class_scopes import ScopeTest

class ScopeExtension(ScopeTest):
    id: str

if __name__ == "__main__":
    sc_ext = ScopeExtension(1)
    sc_ext.test()


