from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
import os


class User:

    def __init__(self, name: str):
        self.name: str = name
        print(f"Initializing {self.name}")

    def __del__(self):
        print(f"Deleting {self.name}")

    def say_hello(self):
        print(f"Hello, I am {self.name}")


class DataUser:

    def __init__(self, name: str, age: int):
        self.name: str = name
        self.age: int = age
        self.__post_init__()

    def __post_init__(self):
        print(f"Post-init for {self.name}, age {self.age}")


def main_func():
    u: User = User("Alice")
    u.say_hello()
    du: DataUser = DataUser("Bob", 30)
    with open("test.txt", "w") as f:
        f.write("Hello Vlang")
    if os.path.exists("test.txt"):
        os.remove("test.txt")


if __name__ == "__main__":
    main_func()
