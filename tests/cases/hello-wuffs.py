import io
from ctypes import c_uint8 as u8
from ctypes import c_uint32 as u32
from dataclasses import dataclass

from py2many.result import Error, Ok, Result


@dataclass
class parser:
    val: u32

    async def parse(self, src: io.RawIOBase) -> Result[u32]:
        while True:
            c: u8 = src.read(1)
            if c == 0:
                return Ok(self.val)

            if (c < 0x30) or (0x39 < c):
                return Error("#not a digit")
            # Rebase from ASCII (0x30 ..= 0x39) to the value (0 ..= 9).
            c -= 0x30

            if self.val < 429_496729:
                self.val = (10 * self.val) + u32(c)
                return Ok(self.val)
            elif (self.val > 429_496729) or (c > 5):
                return Error("#too large")
            self.val = (10 * self.val) + u32(c)
