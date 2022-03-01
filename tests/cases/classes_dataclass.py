from dataclasses import dataclass

@jl_class
@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class Packet:
    val: float

@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class Register:
    PACKET: Packet
    VALUE: int

@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class ValueHolder:
    val: int
    strVal: str

if __name__ == "__main__":
    # Test ValueHolder
    c1 = ValueHolder(2, "1")
    assert c1.__eq__(ValueHolder(val=2, strVal='1'))
    c1.__init__(10, "10")
    assert c1.__eq__(ValueHolder(val=10, strVal='10'))
    c2 = ValueHolder(10, "10")
    assert c1.__le__(c2)
    assert c1.__ge__(c2)
    c2.__init__(11, "10")
    assert c1.__lt__(c2)
    assert c2.__gt__(c1)

    # Test Packet
    c3 = Packet(1.3)
    assert c3.__eq__(Packet(1.3))
    c3.__init__(2.4)
    assert c3.__eq__(Packet(2.4))
    c4 = Packet(2.4)
    assert c3.__le__(c4)
    assert c3.__ge__(c4)
    c4.__init__(2.5)
    assert c3.__lt__(c4)
    assert c4.__gt__(c3)

    # Test Register
    c5 = Register(Packet(1.3), 10)
    assert c5.__eq__(Register(Packet(1.3), 10))
    c5.__init__(Packet(2.2), 10)
    assert c5.__eq__(Register(Packet(2.2), 10))
    c6 = Register(Packet(2.2), 10)
    assert c5.__le__(c6)
    assert c5.__ge__(c6)
    c6.__init__(Packet(2.3), 10)
    assert c5.__lt__(c6)
    assert c6.__gt__(c5)

