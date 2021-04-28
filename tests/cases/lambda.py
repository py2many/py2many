from typing import Callable

# from typing import Protocol
#
# class LambdaFunction(Protocol):
#    def __call__(self, x: int, y: int) -> int:
#        ...


def show():
    myfunc: Callable[[int, int], int] = lambda x, y: x + y
    print(myfunc(1, 2))


if __name__ == "__main__":
    show()
