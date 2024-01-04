from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
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
    b = Register.PACKET(Packet(1.3))
    assert b.is_packet()
    b.packet()
    print("OK")
