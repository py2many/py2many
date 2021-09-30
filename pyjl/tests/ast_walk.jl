import ast
code = "
def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    return 2*a #type=List
"
code2 = "
from adt import sealed
from dataclasses import dataclass


@dataclass
class Packet:
    val: float

@sealed
class Register:
    PACKET: Packet
    VALUE: int


if __name__ == \"__main__\":
    
    a = Register.VALUE(10)
    assert a.is_value()
    a.value()
    b = Register.PACKET(Packet(1.3))
    assert b.is_packet()
    b.packet()
    print(\"OK\")
"
code3 = "
def show_res():
    # value = \" \".join(str(x) for x in range(10) if x > 4 if x < 8)
    value = \"
\".join((str(x)+\" \" +str(y)) for x in range(10) if x > 4 for y in range(8))
    print(value)
"
function main()
tree = parse(ast, code)
tree2 = parse(ast, code2)
tree3 = parse(ast, code3)
println(ast.dump(tree3, 4));
end

main()
