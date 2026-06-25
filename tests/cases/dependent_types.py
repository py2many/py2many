from typing import Annotated

Uid = Annotated[int, lambda uid: 0 < uid < 1000]
Score = Annotated[int, lambda s: 0 <= s <= 100]


def main():
    u: Uid = 42
    s: Score = 85
    print(u)
    print(s)


if __name__ == "__main__":
    main()
