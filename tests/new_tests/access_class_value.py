# On hold until @sealed is solved
from dataclasses import dataclass

@dataclass
class Packet:
    val: float

@dataclass
class Register:
    PACKET: Packet
    VALUE: int

if __name__ == "__main__":
    a = Register(Packet(1.3), 10)
    print("OK")

# Copied from 'cases' folder