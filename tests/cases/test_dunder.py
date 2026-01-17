import os


class User:
    def __init__(self, name: str):
        self.name = name
        print(f"Initializing {self.name}")

    def __del__(self):
        print(f"Deleting {self.name}")

    def say_hello(self):
        print(f"Hello, I am {self.name}")


class DataUser:
    def __init__(self, name: str, age: int):
        self.name = name
        self.age = age
        self.__post_init__()

    def __post_init__(self):
        print(f"Post-init for {self.name}, age {self.age}")


def main():
    u = User("Alice")
    u.say_hello()

    du = DataUser("Bob", 30)

    # Context manager test
    with open("test.txt", "w") as f:
        f.write("Hello Vlang")

    # cleanup test.txt if it exists
    if os.path.exists("test.txt"):
        os.remove("test.txt")


if __name__ == "__main__":
    main()
