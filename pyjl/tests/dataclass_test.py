from dataclasses import dataclass

# (init=True, repr=True, eq=True, order=True, unsafe_hash=False, frozen=False, create_jl_annotation=False)
@dataclass(init=True, eq=True, order=True, unsafe_hash=False, frozen=False, create_jl_annotation=True)
class ValueHolder:
    val: int
    strVal: str

if __name__ == "__main__":
    a = ValueHolder(10, "1")
    print(a)
    ValueHolder.__init__(a, 2, "10")
    print(a)
