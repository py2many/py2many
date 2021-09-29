# On hold until @sealed is solved
from adt import adt as sealed
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

# Copied from 'cases' folder