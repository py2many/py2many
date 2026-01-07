"""Test async with statement"""


class MockAsyncContextManager:
    def __init__(self, name):
        self.name = name

    async def __aenter__(self):
        print(f"Entering {self.name}")
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        print(f"Exiting {self.name}")


async def test_async_with():
    """Test async with statement"""
    async with MockAsyncContextManager("file1") as f:
        print(f"Processing {f.name}")

    async with MockAsyncContextManager("file2"):
        print("Processing without variable")


async def test_nested_async_with():
    """Test nested async with statements"""
    async with MockAsyncContextManager("outer") as outer:
        async with MockAsyncContextManager("inner") as inner:
            print(f"Nested: {outer.name} + {inner.name}")
