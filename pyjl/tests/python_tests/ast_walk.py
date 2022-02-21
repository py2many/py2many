import ast
from decimal import *

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
def generator_func_loop():
    num = 0
    for n in range(0, 3):
        yield num + n

"""

code5 = """
def rock_paper_scissors(playerA: Player, playerB: Player):
    match[playerA.move(), playerB.move()]:
        case [Rock, Scissors]: 
            return "Player A wins"
        case [Paper, Rock]:
            return "Player A wins"
        case [Scissors, Paper]:
            return "Player A wins"
        case [Rock, Paper]:
            return "Player B wins"
        case [Paper, Scissors]:
            return "Player B wins"
        case [Scissors, Rock]: 
            return "Player B wins"
        case _: "Draw"
"""

if __name__ == "__main__":
    # tree = ast.parse(code)
    # tree2 = ast.parse(code2)
    # tree3 = ast.parse(code3)
    # tree4 = ast.parse(code4)
    tree5 = ast.parse(code5)
    print(ast.dump(tree5, indent=4))