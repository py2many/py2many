from enum import Enum


class Colors(str, Enum):
    RED = "red"
    GREEN = "green"
    BLUE = "blue"


def show():
    color_map = {Colors.RED: "1", Colors.GREEN: "2", Colors.BLUE: "3"}
    a = Colors.GREEN
    if a == Colors.GREEN:
        print("green")
    else:
        print("Not green")
    print(len(color_map))


if __name__ == "__main__":
    show()
