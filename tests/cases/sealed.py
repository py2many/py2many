#!/usr/bin/env python3

from dataclasses import dataclass

from adt import adt as sealed


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
    # assert a.value() == 10
    b = Register.PACKET(Packet(1.3))
    assert b.is_packet()
    # assert b.packet().val == 1.3
    b.packet()
    print("OK")
