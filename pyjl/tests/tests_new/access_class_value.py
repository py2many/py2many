# On hold until @sealed is solved
from dataclasses import dataclass

@jl_dataclass # Remove when testing
@dataclass
class Packet:
    val: float

@jl_dataclass # Remove when testing
@dataclass
class Register:
    PACKET: Packet
    VALUE: int

if __name__ == "__main__":
    a = Register(Packet(1.3), 10)
    print("OK")

# Copied from 'cases' folder