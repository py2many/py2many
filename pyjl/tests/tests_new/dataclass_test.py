from dataclasses import dataclass

@jl_dataclass # Remove when testing
@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False)
class ValueHolder:
    val: int
    strVal: str

@jl_dataclass # Remove when testing
@dataclass
class Item:
    id: str
    price_per_unit: float
    quantity: int = 0

if __name__ == "__main__":
    a = ValueHolder(10, "1")
    print(a)
    a.__init__(2, "10")
    print(a)
