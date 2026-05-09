#!/usr/bin/env python3

import asyncio


async def nested() -> int:
    return 42


async def async_main():
    assert await nested() == 42
    print("OK")


if __name__ == "__main__":
    asyncio.run(async_main())
