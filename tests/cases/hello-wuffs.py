import io
from ctypes import c_uint8 as u8
from ctypes import c_uint32 as u32
from dataclasses import dataclass

import pytest

from py2many.result import Error, Ok, Result


@dataclass
class parser:
    val: u32

    async def parse(self, src: io.RawIOBase) -> Result[u32]:
        while True:
            c: u8 = src.read(1)
            if len(c) == 0:
                return Ok(self.val)
            c = c[0]

            if (c < 0x30) or (0x39 < c):
                return Error("#not a digit")
            # Rebase from ASCII (0x30 ..= 0x39) to the value (0 ..= 9).
            c -= 0x30

            if int(self.val.value) < 429_496729:
                self.val = u32((10 * self.val.value) + c)
                continue
            elif int(self.val.value) > 429_496729 or (c > 5):
                return Error("#too large")
            self.val = u32((10 * self.val.value) + c)


@pytest.mark.parametrize(
    "input, expected",
    [
        (b"0", u32(0)),
        (b"12", u32(12)),
        (b"56789", u32(56789)),
        # (1<<32) - 1, aka UINT32_MAX.
        (b"4294967295", u32(4294967295)),
        # (1<<32).
        (b"4294967296", Error("#too large")),
        (b"123456789012", Error("#too large")),
    ],
)
@pytest.mark.asyncio
async def test_parser(input, expected):
    p = parser(u32(0))
    result = await p.parse(io.BytesIO(input))
    if isinstance(result, Ok):
        assert result.value.value == expected.value


if __name__ == "__main__":
    pytest.main(args=[__file__])
    print("OK")
