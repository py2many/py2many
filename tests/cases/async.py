#!/usr/bin/env python3

import asyncio


async def async_gen():
    for i in range(3):
        yield i


async def show_async():
    # Async for
    async for val in async_gen():
        print(val)


def show():
    # Run async function
    asyncio.run(show_async())


if __name__ == "__main__":
    show()
