#!/usr/bin/env python3

import asyncio


class AsyncContextManager:
    async def __aenter__(self):
        print("entering async context")
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        print("exiting async context")
        return False


async def async_gen():
    for i in range(3):
        yield i


async def show_async():
    # Async for
    async for val in async_gen():
        print(val)

    # Async with
    async with AsyncContextManager() as cm:
        print("inside async with")


def show():
    # Run async function
    asyncio.run(show_async())


if __name__ == "__main__":
    show()
