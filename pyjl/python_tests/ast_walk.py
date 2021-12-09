import ast

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
from dataclasses import dataclass

@dataclass
class Packet:
    val: float

@dataclass
class Register:
    PACKET: Packet
    VALUE: int

if __name__ == "__main__":
    a = List()
    print("OK")
"""



if __name__ == "__main__":
    tree = ast.parse(code)
    tree2 = ast.parse(code2)
    # tree3 = ast.parse(code3)
    tree4 = ast.parse(code4)
    # print(ast.dump(tree, indent=4))
    # print(ast.dump(tree2, indent=4))
    # print(ast.dump(tree3, indent=4))
    print(ast.dump(tree4, indent=4))