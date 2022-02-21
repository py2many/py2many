from dataclasses import dataclass


@dataclass
class Packet:
    val: float

@dataclass
class Register:
    PACKET: Packet
    VALUE: int

@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class ValueHolder:
    val: int
    strVal: str

@dataclass
class Item:
    id: str
    price_per_unit: float
    quantity: int = 0

if __name__ == "__main__":
    a = ValueHolder(10, "1")
    assert a == ValueHolder(val=10, strVal='1')
    a.__init__(2, "10")
    assert a == ValueHolder(val=2, strVal='10')

    a = Register(Packet(1.3), 10)