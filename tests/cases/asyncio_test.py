
#!/usr/bin/env python3

import asyncio
from turtle import listen


async def nested() -> int:
    return 42


async def async_main():
    assert await nested() == 42
    print("OK")

# From Eric Engheim at: 
#   https://levelup.gitconnected.com/coroutines-and-tasks-in-julia-and-python-c82f7ec52a9e
async def echo_server():
   server = listen(2001)
   while True:
       sock = await server.accept()
       async def writer():
           while sock.isopen():
               data = await sock.readline()
               await sock.write(data.upper())
       await writer()


if __name__ == "__main__":
    asyncio.run(async_main())
    # More comples example
    asyncio.run(echo_server())
