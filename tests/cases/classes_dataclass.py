from dataclasses import dataclass

# @jl_dataclass # For PyJL
@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class Packet:
    val: float


# @jl_dataclass # For PyJL
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
    c1 = ValueHolder(10, "10")
    assert c1.__eq__(ValueHolder(val=10, strVal="10"))
    c2 = ValueHolder(10, "10")
    assert c1.__le__(c2)
    assert c1.__ge__(c2)
    c1 = ValueHolder(val=11, strVal="10")
    assert c2.__lt__(c1)
    assert c1.__gt__(c2)

    # Test Packet
    c3 = Packet(2.4)
    assert c3.__eq__(Packet(2.4))
    c4 = Packet(2.4)
    assert c3.__le__(c4)
    assert c3.__ge__(c4)
    c3 = Packet(2.5)
    assert c4.__lt__(c3)
    assert c3.__gt__(c4)

    # Test Register
    c5 = Register(Packet(2.2), 10)
    assert c5.__eq__(Register(Packet(2.2), 10))
    c6 = Register(Packet(2.2), 10)
    assert c5.__le__(c6)
    assert c5.__ge__(c6)
    c5 = Register(Packet(2.3), 10)
    assert c6.__lt__(c5)
    assert c5.__gt__(c6)
