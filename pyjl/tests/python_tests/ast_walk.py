import ast
from cmath import sin
from decimal import *
from statistics import mode

code = """
def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    return 2*a #type=List
"""

code2 = """
from adt import sealed
from dataclasses import dataclass


@dataclass
class Packet:
    val: float

@sealed
class Register:
    PACKET: Packet
    VALUE: int


if __name__ == "__main__":
    
    a = Register.VALUE(10)
    assert a.is_value()
    a.value()
    b = Register.PACKET(Packet(1.3))
    assert b.is_packet()
    b.packet()
    print("OK")
"""

code3 = """
def show_res():
    # value = " ".join(str(x) for x in range(10) if x > 4 if x < 8)
    value = "\n".join((str(x)+" " +str(y)) for x in range(10) if x > 4 for y in range(8))
    print(value)
"""

code4 = """
class something:
    id: str

class Hello(something):
    def __init__():
        pass

    def test(self):
        print("test")

"""

code5 = """
'''class Colors(IntEnum):
    RED = auto()
    GREEN = auto()
    BLUE = auto()'''
"""

if __name__ == "__main__":
    # tree = ast.parse(code)
    # tree2 = ast.parse(code2)
    # tree3 = ast.parse(code3)
    # tree4 = ast.parse(code4)
    tree5 = ast.parse(code5, type_comments=True)
    print(ast.dump(tree5, indent=4))