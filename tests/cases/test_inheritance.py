class Parent:
    def __init__(self, x: int):
        self.x = x


class Child(Parent):
    def __init__(self, x: int, y: int):
        super().__init__(x)
        self.y = y


if __name__ == "__main__":
    c = Child(10, 20)
    print(c.x)
    print(c.y)
